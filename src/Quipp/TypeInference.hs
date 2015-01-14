{-# LANGUAGE TupleSections, ViewPatterns #-}

module Quipp.TypeInference where

import Debug.Trace
import Data.Function (fix)
import Data.List (elemIndex)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Applicative ((<$>), (<*>))
import Control.Monad (liftM, zipWithM, forM, replicateM)
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad.Reader.Class (ask, local)
import Control.Monad.State (get, put)
import Control.Monad.State.Lazy (State, runState, StateT, runStateT)
import Control.Monad.Trans (lift)

import Quipp.ExpFam
import Quipp.Factor
import Quipp.GraphBuilder
import Quipp.Value
import Quipp.Util

data TypeExpr = VarTExpr String | ConstTExpr String | AppTExpr TypeExpr TypeExpr deriving (Eq, Ord)

instance Show TypeExpr where
  showsPrec _ (VarTExpr v) = showString v
  showsPrec _ (ConstTExpr s) = showString s
  showsPrec p (AppTExpr (AppTExpr (ConstTExpr "->") a) r) =
    showParen (p > 5) $ showsPrec 6 a . showString " -> " . showsPrec 5 r
  showsPrec p (AppTExpr a b) =
    showParen (p > 10) $ showsPrec 10 a . showString " " . showsPrec 11 b

type AdtDefinition = (String, [String], [(String, [TypeExpr])])

data PatternExpr = VarPExpr String | ConstrPExpr String [PatternExpr] deriving (Eq, Ord, Show)

data Expr = VarExpr String | WithTypeExpr Expr TypeExpr | LambdaExpr String Expr | AppExpr Expr Expr | DefExpr [(String, Expr)] Expr | LiteralExpr Value | TypeLiteralExpr TypeExpr | AdtDefExpr AdtDefinition Expr | CaseExpr Expr [(PatternExpr, Expr)] | ErrorExpr String deriving (Eq, Ord)

instance Show Expr where
  showsPrec _ (VarExpr v) = showString v
  showsPrec p (LiteralExpr v) = showsPrec p v
  showsPrec p (WithTypeExpr e t) =
    showParen (p > 3) $ showsPrec 1 e . showString " : " . showsPrec 3 t
  showsPrec p (LambdaExpr v b) =
    showParen (p > 1) $ showString "\\" . showString v . showString " -> " . showsPrec 1 b
  showsPrec p (AppExpr (LambdaExpr s b) v) =
    showParen (p > 1) $ showString "let " . showString s . showString " = " . showsPrec 0 v . showString ";\n" . showsPrec 0 b
  showsPrec p (AppExpr a b) =
    showParen (p > 10) $ showsPrec 10 a . showString " " . showsPrec 11 b
  showsPrec p (DefExpr varvals b) =
    showParen (p > 1) $ showString "def " . (foldr1 (.) [showString s . showString " = " . showsPrec 0 v . showString ";\n" | (s, v) <- varvals]) . showsPrec 0 b
  -- TODO
  showsPrec p (AdtDefExpr (name, params, constrs) body) =
    showParen (p > 1) $ showString "data " . showString (unwords (name : params)) . showString " = " . showsPrec 0 constrs . showString ";\n" . showsPrec 0 body
  showsPrec p (CaseExpr ex cases) = showString (show ("case", ex, cases))
  showsPrec p (ErrorExpr err) = showString (show ("err", err))
  showsPrec p (TypeLiteralExpr t) = showsPrec p t

constTrue = constValue boolValueExpFam (BoolValue True)
constFalse = constValue boolValueExpFam (BoolValue False)

type TypeId = Int

functionType a b = AppTExpr (AppTExpr (ConstTExpr "->") a) b

splitAppType :: TypeExpr -> (TypeExpr, [TypeExpr])
splitAppType (AppTExpr a b) =
  let (head, args) = splitAppType a in (head, args ++ [b])
splitAppType other = (other, [])


splitFunctionType :: TypeExpr -> ([TypeExpr], TypeExpr)
splitFunctionType (AppTExpr (AppTExpr (ConstTExpr "->") a) b) =
  let (args, res) = splitFunctionType b in (a:args, res)
splitFunctionType other = ([], other)


reduceTypeShallowIn :: Map String TypeExpr -> TypeExpr -> TypeExpr

reduceTypeShallowIn m t@(VarTExpr v) = case Map.lookup v m of
  Nothing -> t
  Just t' -> reduceTypeShallowIn m t'
reduceTypeShallowIn _ other = other

reduceTypeDeepIn :: Map String TypeExpr -> TypeExpr -> TypeExpr
reduceTypeDeepIn m t = case reduceTypeShallowIn m t of
  AppTExpr fun arg -> AppTExpr (reduceTypeDeepIn m fun) (reduceTypeDeepIn m arg)
  other -> other

simpleValueType :: Value -> TypeExpr
simpleValueType (DoubleValue _) = ConstTExpr "Double"
simpleValueType (BoolValue _) = ConstTExpr "Bool"

-- We can't get the type of an arbitrary GraphValue.  However, we can do some
-- sanity checks to make sure it's not completely the wrong type.


-- perhaps the rest should be split up?
--

type CompoundValueDistr = [(VarId, String, [GraphValue])]

data GraphValue = VarGraphValue VarId | LambdaGraphValue (GraphValue -> GraphBuilder Value GraphValue) | TypeGraphValue TypeExpr | CompoundGraphValue CompoundValueDistr

data FrozenGraphValue = FValueGraphValue Value | FCompoundGraphValue String [FrozenGraphValue] | FTypeGraphValue TypeExpr deriving (Eq, Ord)

showCompound :: Show f => String -> [f] -> String
showCompound c fs = c ++ concatMap ((' ':) . show) fs

instance Show GraphValue where
  show (VarGraphValue varid) = "$" ++ show varid
  show (LambdaGraphValue _) = "#lambda"
  show (CompoundGraphValue []) = "<undefined>"
  show (CompoundGraphValue [(v, c, fs)]) = "(" ++ showCompound c fs ++ ")"
  show (CompoundGraphValue ((v, c, fs):rest)) =
    "(if $" ++ show v ++ " then " ++ showCompound c fs ++ " else " ++ show (CompoundGraphValue rest) ++ ")"
  show (TypeGraphValue t) = "#" ++ show t

instance Show FrozenGraphValue where
  show (FValueGraphValue v) = show v
  show (FCompoundGraphValue c fs) = "(" ++ showCompound c fs ++ ")"
  show (FTypeGraphValue t) = "#" ++ show t

freezeGraphValue :: (VarId -> Value) -> GraphValue -> FrozenGraphValue
freezeGraphValue f (VarGraphValue v) = FValueGraphValue $ f v
freezeGraphValue _ (TypeGraphValue t) = FTypeGraphValue t
freezeGraphValue f (CompoundGraphValue []) = undefined
freezeGraphValue f (CompoundGraphValue ((v, c, fs):rest)) = case f v of
  BoolValue True -> FCompoundGraphValue c (map (freezeGraphValue f) fs)
  BoolValue False -> freezeGraphValue f (CompoundGraphValue rest)
freezeGraphValue _ other = error "Cannot freeze lambdas"

unfreezeGraphValue :: FrozenGraphValue -> GraphBuilder Value GraphValue
unfreezeGraphValue (FCompoundGraphValue c fs) = do
  true <- constTrue
  fs' <- mapM unfreezeGraphValue fs
  return $ CompoundGraphValue [(true, c, fs')]
unfreezeGraphValue (FValueGraphValue value) =
  VarGraphValue <$> constValue (expFamForType (simpleValueType value)) value
unfreezeGraphValue (FTypeGraphValue t) = return $ TypeGraphValue t
unfreezeGraphValue other = error ("Cannot freeze " ++ show other)

expFamForType :: TypeExpr -> ExpFam Value
expFamForType (ConstTExpr "Double") = gaussianValueExpFam
expFamForType (ConstTExpr "Bool") = boolValueExpFam
expFamForType t = error $ "Can't get exponential family for type " ++ show t

multiArgFunction :: Int -> ([GraphValue] -> GraphBuilder Value GraphValue) -> GraphBuilder Value GraphValue
multiArgFunction 0 fn = fn []
multiArgFunction nArgs fn = return $ LambdaGraphValue $ \firstArg -> multiArgFunction (nArgs - 1) (\restArgs -> fn (firstArg : restArgs))

andVariables :: [VarId] -> GraphBuilder Value VarId
andVariables [] = constTrue
andVariables (x:xs) = do
  true <- constTrue
  rest <- andVariables xs
  VarGraphValue res <- ifThenElse x (VarGraphValue true) (VarGraphValue rest)
  return res


interpretPattern :: PatternExpr -> GraphValue -> GraphBuilder Value (Maybe (VarId, [(String, GraphValue)]))
interpretPattern (VarPExpr var) value = do
  true <- constTrue
  return $ Just (true, [(var, value)])
interpretPattern (ConstrPExpr constr fields) (CompoundGraphValue alts) = case elemIndex constr (map snd3 alts) of
  Nothing -> do
    false <- constFalse
    return Nothing
  Just index -> do
    let (_, _, fs) = alts !! index
    fieldMatches <- zipWithM interpretPattern fields fs
    case sequence fieldMatches of
      Nothing -> return Nothing
      Just fieldMatches' -> do
        andVar <- andVariables (take (index + 1) (map fst3 alts) ++ map fst fieldMatches')
        return $ Just (andVar, concat (map snd fieldMatches'))

unitGraphValue = do
  true <- constTrue
  return $ CompoundGraphValue [(true, "Unit", [])]

pairGraphValue v1 v2 = do
  true <- constTrue
  return $ CompoundGraphValue [(true, "Pair", [v1, v2])]

interpretExpr :: Map String (Map String AdtDefinition -> GraphBuilder Value GraphValue) -> Map String AdtDefinition -> Expr -> GraphBuilder Value GraphValue

interpretExpr _ _ x | trace ("\ninterpret " ++ show x) False = undefined

interpretExpr m adts (VarExpr var) = case Map.lookup var m of
  Nothing -> error ("cannot find variable " ++ var)
  Just val -> val adts

interpretExpr m adts (LambdaExpr param body) = return $ LambdaGraphValue $
  \arg -> interpretExpr (Map.insert param (const $ return arg) m) adts body

interpretExpr m adts (AppExpr fun arg) = do
  funVal <- interpretExpr m adts fun
  argVal <- interpretExpr m adts arg
  case funVal of
    LambdaGraphValue f -> f argVal
    CompoundGraphValue alts -> return $ CompoundGraphValue [(v, c, fs ++ [argVal]) | (v, c, fs) <- alts]
    TypeGraphValue ft -> do
      case argVal of
        TypeGraphValue at -> return $ TypeGraphValue (AppTExpr ft at)
        _ -> error $ "Cannot apply type to non-type " ++ show argVal
    _ -> error $ "Function in application expression is not actually a function: " ++ show funVal

interpretExpr m adts (DefExpr varvals body) = do
  let newM = insertAll [(var, \_ -> interpretExpr newM adts val) | (var, val) <- varvals] m
  interpretExpr newM adts body

interpretExpr m adts (LiteralExpr value) = do
  var <- newVar (expFamForType (simpleValueType value))
  newConstFactor var value
  return $ VarGraphValue var

interpretExpr m adts (TypeLiteralExpr t) = return $ TypeGraphValue t

interpretExpr m adts (AdtDefExpr defn@(typeName, typeArgs, alts) body) = do
  let wrappedType = foldl AppTExpr (ConstTExpr typeName) (map VarTExpr typeArgs)
  let defValues = [(constr, const $ unfreezeGraphValue (FCompoundGraphValue constr [])) | (constr, _) <- alts] ++
                  [("T" ++ typeName, const $ return $ TypeGraphValue $ ConstTExpr typeName)]
  interpretExpr (insertAll defValues m) (Map.insert typeName defn adts) body

-- TODO
interpretExpr m adts (ErrorExpr err) = unitGraphValue

interpretExpr m adts (CaseExpr valueExpr cases) = do
  value <- interpretExpr m adts valueExpr
  let matchAny [] = interpretExpr m adts (ErrorExpr "all alternatives failed!")
      matchAny ((p, b):rest) = do
        nonMatchedBranch <- matchAny rest
        matchResult <- interpretPattern p value
        case matchResult of
          Nothing -> return nonMatchedBranch
          Just (matched, varvals) -> do
            let varvals' = [(v, const $ return val) | (v, val) <- varvals]
            matchedBranch <- interpretExpr (insertAll varvals' m) adts b
            ifThenElse matched matchedBranch nonMatchedBranch
  matchAny cases


interpretExpr _ _ other = error $ "Cannot interpret expr " ++ show other

notVar :: VarId -> GraphBuilder Value VarId
notVar x = do
  y <- newVar boolValueExpFam
  newFactor notFactor [y, x]
  return y

-- TODO: this might be wrong due to multiple trues
ifThenElse pvar (CompoundGraphValue left) (CompoundGraphValue right) =
  let oneSideOnly flipper ((lv, lc, lf):lrest) rrest = do
        rv <- constFalse
        VarGraphValue v' <- flipper (ifThenElse pvar) (VarGraphValue lv) (VarGraphValue rv)
        CompoundGraphValue rest <- flipper (ifThenElse pvar) (CompoundGraphValue lrest) (CompoundGraphValue rrest)
        return $ CompoundGraphValue ((v', lc, lf):rest)
      leftOnly = oneSideOnly id left right
      rightOnly = oneSideOnly flip right left
  in case (left, right) of
    ([], []) -> return $ CompoundGraphValue []
    (_, []) -> leftOnly
    ([], _) -> rightOnly
    ((lv, lc, lf):lrest, (rv, rc, rf):rrest) -> case compare (lc, length lf) (rc, length rf) of
      LT -> leftOnly
      GT -> rightOnly
      EQ -> do
        VarGraphValue v' <- ifThenElse pvar (VarGraphValue lv) (VarGraphValue rv)
        firstFields <- zipWithM (ifThenElse pvar) lf rf
        CompoundGraphValue rest <- ifThenElse pvar (CompoundGraphValue lrest) (CompoundGraphValue rrest)
        return $ CompoundGraphValue ((v', lc, firstFields) : rest)


ifThenElse pvar (LambdaGraphValue f) (LambdaGraphValue g) =
  return $ LambdaGraphValue $ \x -> do
    fx <- f x
    gx <- g x
    ifThenElse pvar fx gx

ifThenElse pvar (VarGraphValue v1) (VarGraphValue v2) = do
  ef <- getVarExpFam v1
  v3 <- newVar ef
  newFactor (ifThenElseFactor ef) [v3, pvar, v1, v2]
  return (VarGraphValue v3)

ifThenElse pvar left right = error $ "Cannot have an if-then-else that might return objects of different types: " ++ show left ++ ", " ++ show right

unifyGraphValues :: GraphValue -> GraphValue -> GraphBuilder Value GraphValue
unifyGraphValues (VarGraphValue a) (VarGraphValue b) = liftM VarGraphValue $ conditionEqual a b
unifyGraphValues (CompoundGraphValue left) (CompoundGraphValue right) =
  let oneSideOnly ((lv, lc, lf):lrest) rrest = do
        rv <- constFalse
        conditionEqual lv rv
        unifyGraphValues (CompoundGraphValue lrest) (CompoundGraphValue rrest)
      leftOnly = oneSideOnly left right
      rightOnly = oneSideOnly right left
  in case (left, right) of
    ([], []) -> return $ CompoundGraphValue []
    (_, []) -> leftOnly
    ([], _) -> rightOnly
    ((lv, lc, lf):lrest, (rv, rc, rf):rrest) -> case compare (lc, length lf) (rc, length rf) of
      LT -> leftOnly
      GT -> rightOnly
      EQ -> do
        v' <- conditionEqual lv rv
        -- TODO: this seems a little wrong
        fs' <- zipWithM unifyGraphValues lf rf
        CompoundGraphValue rest' <- unifyGraphValues (CompoundGraphValue lrest) (CompoundGraphValue rrest)
        return $ CompoundGraphValue ((v', lc, fs') : rest')
unifyGraphValues v1 v2 = error ("Cannot unify values " ++ show v1 ++ " and " ++ show v2)

expandAdt :: AdtDefinition -> [TypeExpr] -> [(String, [TypeExpr])]
expandAdt (_, paramNames, alts) params =
  [(constr, map (reduceTypeDeepIn (Map.fromList (zipSameLength paramNames params))) fs) |
   (constr, fs) <- alts]

expandAdtInEnv :: Map String AdtDefinition -> TypeExpr -> Maybe [(String, [TypeExpr])]
expandAdtInEnv adts (splitAppType -> (ConstTExpr adtTypeName, params)) =
  case Map.lookup adtTypeName adts of
    Nothing -> Nothing
    Just defn -> Just (expandAdt defn params)
expandAdtInEnv _ _ = Nothing



typeToExpFams :: Map String AdtDefinition -> TypeExpr -> [ExpFam Value]
typeToExpFams adts (expandAdtInEnv adts -> Just alts) =
  replicate (length alts) boolValueExpFam ++ do
    (_, fieldTypes) <- alts
    fieldTypes >>= typeToExpFams adts

typeToExpFams _ other = error ("Cannot get exponential family for type: " ++ show other)

graphValueEmbeddedVars :: Map String AdtDefinition -> TypeExpr -> GraphValue -> [VarId]
graphValueEmbeddedVars _ _ (VarGraphValue v) = [v]
graphValueEmbeddedVars adts (expandAdtInEnv adts -> Just alts) (CompoundGraphValue constrs) =
  map fst3 constrs ++ do
    -- TODO: handle subset
    ((constrName, fieldTypes), (_, constrName', fs)) <- zipSameLength alts constrs
    if constrName == constrName' then return () else undefined
    (typ, field) <- zipSameLength fieldTypes fs
    graphValueEmbeddedVars adts typ field
graphValueEmbeddedVars _ _ (LambdaGraphValue _) =
  error "Cannot get embedded variables in LambdaGraphValue"

popState :: State [a] a
popState = do
  (x:xs) <- get
  put xs
  return x

varsToGraphValue' :: Map String AdtDefinition -> TypeExpr -> State [VarId] GraphValue
varsToGraphValue' _ (ConstTExpr x) | elem x ["Bool", "Double"] = do
  (v:vs) <- get
  put vs
  return $ VarGraphValue v
varsToGraphValue' adts (expandAdtInEnv adts -> Just alts) = do
  boolVars <- replicateM (length alts) popState
  alts <- forM (zip alts boolVars) $ \((constrName, fieldTypes), boolVar) -> do
    fieldValues <- mapM (varsToGraphValue' adts) fieldTypes
    return (boolVar, constrName, fieldValues)
  return $ CompoundGraphValue alts
varsToGraphValue' _ other =
  error ("Cannot get graph value for type: " ++ show other)

varsToGraphValue :: Map String AdtDefinition -> TypeExpr -> [VarId] -> GraphValue
varsToGraphValue adts t vars = case runState (varsToGraphValue' adts t) vars of
  (result, []) -> result
  other -> error $ "Too many variables (" ++ show (length vars) ++ ") for type " ++ show t

-- fmapNewtype :: TypeExpr -> String -> (GraphValue -> GraphBuilder Value GraphValue) -> GraphValue -> GraphBuilder Value GraphValue
-- fmapNewtype (VarTExpr var) v f val | var == v = f val
--                                    | otherwise = return val
-- fmapNewtype (ConstTExpr _) _ _ val = return val
-- fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "_Pair") atype) btype) v f (PairGraphValue a b) =
--   PairGraphValue <$> fmapNewtype atype v f a <*> fmapNewtype btype v f b
-- fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "_Either") ltype) rtype) v f (EitherGraphValue c l r) =
--   EitherGraphValue c <$> fmapNewtype ltype v f l <*> fmapNewtype rtype v f r
-- fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "_Either") ltype) rtype) v f (PureLeftGraphValue l) =
--   PureLeftGraphValue <$> fmapNewtype ltype v f l
-- fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "_Either") ltype) rtype) v f (PureRightGraphValue r) =
--   PureRightGraphValue <$> fmapNewtype rtype v f r
-- fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "->") argtype) rettype) v f (LambdaGraphValue lam) =
--   -- TODO: v should not appear in argtype
--   return $ LambdaGraphValue $ \arg -> lam arg >>= fmapNewtype rettype v f

const2 = const . const

defaultContext :: Map String (Map String AdtDefinition -> GraphBuilder Value GraphValue)
defaultContext = Map.fromList [
  -- unify :: a -> a -> a
  -- conditions on its arguments being equal, returning one of them
  ("unify",
   const $ return $ LambdaGraphValue $ \v1 ->
     return $ LambdaGraphValue $ \v2 -> unifyGraphValues v1 v2),
  -- -- cata :: Functor f => (f a -> a) -> Mu f -> a
  -- -- cata f = f . fmap (cata f) . unMu
  -- ("cata",
  --  do f <- newVarType "cata_f"
  --     a <- newVarType "cata_a"
  --     return $ functionType (functionType (AppTExpr f a) a) $ functionType (muType f) a,
  --  const2 $ return $ LambdaGraphValue $ \(LambdaGraphValue cataFun) ->
  --    return $ LambdaGraphValue $ fix $ \doCata -> \(MuGraphValue (typeName, typeParams, typeBody) innerValue) -> do
  --      fmapped <- fmapNewtype typeBody (last typeParams) doCata innerValue
  --      cataFun fmapped
  -- ),
  -- TODO bayes net!
  ("uniformBool",
   const $ return $ LambdaGraphValue $ \_ -> do
     v <- newVar boolValueExpFam
     newFactor (expFamFactor boolValueExpFam [] ([0.0], [[]])) [v]
     return $ VarGraphValue v),
  ("standardNormal",
   const $ return $ LambdaGraphValue $ \_ -> do
     v <- newVar gaussianValueExpFam
     newFactor (expFamFactor gaussianValueExpFam [] ([0.0, -0.5], [[]])) [v]
     return $ VarGraphValue v),
  ("TDouble", const $ return $ TypeGraphValue $ ConstTExpr "Double"),
  -- TODO: somehow this has to be lazy.  See what it's called with, then
  -- make a different function for each?  Or just take arg type as an argument.
  ("randFunction",
   \adts ->
     return $ LambdaGraphValue $ \argTypeValue -> case argTypeValue of
       TypeGraphValue argType -> return $ LambdaGraphValue $ \resTypeValue -> case resTypeValue of
         TypeGraphValue resType -> do
           let argExpFams = typeToExpFams adts argType
               resExpFams = typeToExpFams adts resType
           rfs <- mapM (flip newRandFun argExpFams) resExpFams
           return $ LambdaGraphValue $ \argValue -> do
             let argVars = graphValueEmbeddedVars adts argType argValue
             resVars <- mapM (flip newSampleFromRandFun argVars) rfs
             return $ varsToGraphValue adts resType resVars
         other -> error $ "randFunction called with non-type second argument " ++ show other
       other -> error $ "randFunction called with non-type first argument " ++ show other
  )
  ]
