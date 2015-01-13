{-# LANGUAGE TupleSections, ViewPatterns #-}

module Quipp.TypeInference where

import Debug.Trace
import Data.Function (fix)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Applicative ((<$>), (<*>))
import Control.Monad (liftM, zipWithM, forM)
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

type NewTypeDefinition = (String, [String], TypeExpr)

  -- Un-annotated expressions.
data Expr = VarExpr String | WithTypeExpr Expr TypeExpr | LambdaExpr String Expr | AppExpr Expr Expr | DefExpr [(String, Expr)] Expr | LiteralExpr Value | TypeLiteralExpr TypeExpr | NewTypeExpr NewTypeDefinition Expr deriving (Eq, Ord)

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
  showsPrec p (NewTypeExpr (name, params, inner) body) =
    showParen (p > 1) $ showString "newtype " . showString (unwords (name : params)) . showString " = " . showsPrec 0 inner . showString ";\n" . showsPrec 0 body
  showsPrec p (TypeLiteralExpr t) = showsPrec p t

type TypeId = Int

functionType a b = AppTExpr (AppTExpr (ConstTExpr "->") a) b
pairType a b = AppTExpr (AppTExpr (ConstTExpr "_Pair") a) b
eitherType a b = AppTExpr (AppTExpr (ConstTExpr "_Either") a) b
muType f = AppTExpr (ConstTExpr "Mu") f

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

showCompound :: Show f => (VarId, String, [f]) -> String
showCompound c fs = c ++ concatMap ((' ':) . show) fs

instance Show GraphValue where
  show (VarGraphValue varid) = "$" ++ show varid
  show (LambdaGraphValue _) = "#lambda"
  show (CompoundGraphValue []) = "<undefined>"
  show (CompoundGraphValue [(v, c, fs)]) = "(" ++ showCompound c fs ++ ")"
  show (CompoundGraphValue ((v, c, fs):rest) =
    "(if $" ++ show v ++ " then " ++ showCompound c fs ++ " else " ++ show (CompoundGraphValue rest) ++ ")"
  show (TypeGraphValue t) = "#" ++ show t

instance Show FrozenGraphValue where
  show (FValueGraphValue v) = show v
  show (FCompoundGraphValue c fs) = "(" ++ showCompound c fs ++ ")"
  show (FTypeGraphValue t) = "#" ++ show t

freezeGraphValue :: (VarId -> Value) -> GraphValue -> FrozenGraphValue
freezeGraphValue _ UnitGraphValue = FUnitGraphValue
freezeGraphValue f (VarGraphValue v) = FValueGraphValue $ f v
freezeGraphValue _ (TypeGraphValue t) = FTypeGraphValue t
freezeGraphValue f (CompoundGraphValue []) = undefined
freezeGraphValue f (CompoundGraphValue ((v, c, fs):rest)) = case f v of
  BoolValue True -> FCompoundGraphValue c (map (freezeGraphValue f) fs)
  BoolValue False -> freezeGraphValue f (CompoundGraphValue rest)
freezeGraphValue _ other = error "Cannot freeze lambdas"

unfreezeGraphValue :: FrozenGraphValue -> GraphBuilder Value GraphValue
unfreezeGraphValue (FCompoundGraphValue c fs) = do
  constTrue <- constValue boolValueExpFam (BoolValue False)
  fs' <- mapM unfreezeGraphValue fs
  return $ CompoundGraphValue [(constTrue, c, fs')]
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

expandNewType :: NewTypeDefinition -> [TypeExpr] -> TypeExpr
expandNewType (_, paramVars, inner) params =
  reduceTypeDeepIn (foldr (uncurry Map.insert) Map.empty (zipSameLength paramVars params)) inner


-- interpretPattern :: PatternExpr -> GraphValue -> GraphBuilder Value (Maybe [(String, GraphValue)])
  -- interpretPattern (VarPExpr var) value = return $ Just [(var, value)]
  -- interpretPattern (ConstrPExpr constr 

interpretExpr :: Map String (Map String NewTypeDefinition -> GraphBuilder Value GraphValue) -> Map String NewTypeDefinition -> Expr -> GraphBuilder Value GraphValue

interpretExpr _ _ x | trace ("\ninterpret " ++ show x) False = undefined

interpretExpr m nts (VarExpr var) = case Map.lookup var m of
  Nothing -> error ("cannot find variable " ++ var)
  Just val -> val nts

interpretExpr m nts (LambdaExpr param body) = return $ LambdaGraphValue $
  \arg -> interpretExpr (Map.insert param (const $ return arg) m) nts body

interpretExpr m nts (AppExpr fun arg) = do
  funVal <- interpretExpr m nts fun
  argVal <- interpretExpr m nts arg
  case funVal of
    LambdaGraphValue f -> f argVal
    CompoundGraphValue alts = CompoundGraphValue $ [(v, c, fs ++ [argVal]) | (v, c, fs) <- alts]
    TypeGraphValue ft -> do
      case argVal of
        TypeGraphValue at -> return $ TypeGraphValue (AppTExpr ft at)
        _ -> error $ "Cannot apply type to non-type " ++ show argVal
    _ -> error $ "Function in application expression is not actually a function: " ++ show funVal

interpretExpr m nts (DefExpr varvals body) = do
  let newM = insertAll [(var, \_ -> interpretExpr newM nts val) | (var, val) <- varvals] m
  interpretExpr newM nts body

interpretExpr m nts (LiteralExpr value) = do
  var <- newVar (expFamForType (simpleValueType value))
  newConstFactor var value
  return $ VarGraphValue var

interpretExpr m nts (TypeLiteralExpr t) = return $ TypeGraphValue t

interpretExpr m nts (NewTypeExpr defn@(typeName, typeArgs, innerType) body) = do
  let wrappedType = foldl AppTExpr (ConstTExpr typeName) (map VarTExpr typeArgs)
  let valueToType (TypeGraphValue t) = t
  interpretExpr (Map.insert ("Make" ++ typeName) idFun $ Map.insert ("un" ++ typeName) idFun $ Map.insert ("T" ++ typeName) (const $ return $ TypeGraphValue $ ConstTExpr typeName) m) (Map.insert typeName defn nts) body

interpretExpr _ _ other = error $ "Cannot interpret expr " ++ show other

notVar :: VarId -> GraphBuilder Value VarId
notVar x = do
  y <- newVar boolValueExpFam
  newFactor notFactor [y, x]
  return y

ifThenElse pvar (CompoundGraphValue left) (CompoundGraphValue right) =
  let oneSideOnly flipper ((lv, lc, lf):lrest) rrest = do
        rv <- constValue boolValueExpFam (BoolValue False)
        VarGraphValue v' <- flipper (ifThenElse pvar) (VarGraphValue lv) (VarGraphValue rv)
        rest <- flipper (ifThenElse pvar) (CompoundGraphValue lrest) rrest
        return $ CompoundGraphValue ((v', lc, lf):rest)
      leftOnly = oneSideOnly id left right
      rightOnly l r = oneSideOnly flip right left
  case (left, right) of
    ([], []) -> return $ CompoundGraphValue []
    (_, []) -> leftOnly
    ([], _) -> rightOnly
    ((lv, lc, lf):lrest, (rv, rc, rf):rrest) -> case compare (lc, length lf) (rc, length rf) of
      LT -> leftOnly
      GT -> rightOnly
      EQ -> do
        VarGraphValue v' <- ifThenElse pvar (VarGraphValue lv) (VarGraphValue rv)
        firstFields <- zipWithM (ifThenElse pvar) lf rf
        rest <- ifThenElse pvar (CompoundGraphValue lrest) (CompoundGraphValue rrest)
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
        rv <- constValue boolValueExpFam (BoolValue False)
        conditionEqual lv rv
        unifyGraphValues (CompoundGraphValue lrest) (CompoundGraphValue rrest)
      leftOnly = oneSideOnly left right
      rightOnly l r = oneSideOnly right left
  case (left, right) of
    ([], []) -> return $ CompoundGraphValue []
    (_, []) -> leftOnly
    ([], _) -> rightOnly
    ((lv, lc, lf):lrest, (rv, rc, rf):rrest) -> case compare (lc, length lf) (rc, length rf) of
      LT -> leftOnly
      GT -> rightOnly
      EQ -> do
        v' <- conditionEqual lv rv
        fs' <- zipWithM conditionEqual lf rf
        rest' <- unifyGraphValues (CompoundGraphValue lrest) (CompoundGraphValue rrest)
        return $ CompoundGraphValue ((v', lc, fs') : rest')
unifyGraphValues v1 v2 = error ("Cannot unify values " ++ show v1 ++ " and " ++ show v2)


typeToExpFams :: Map String NewTypeDefinition -> TypeExpr -> [ExpFam Value]
typeToExpFams _ (ConstTExpr "_Unit") = []
typeToExpFams _ t@(ConstTExpr _) = [expFamForType t]
typeToExpFams nts (AppTExpr (AppTExpr (ConstTExpr "_Pair") a) b) =
  typeToExpFams nts a ++ typeToExpFams nts b
typeToExpFams nts (AppTExpr (AppTExpr (ConstTExpr "_Either") a) b) =
  [boolValueExpFam] ++ typeToExpFams nts a ++ typeToExpFams nts b
typeToExpFams nts (splitAppType -> (ConstTExpr newTypeName, params)) =
  case Map.lookup newTypeName nts of
    Nothing -> error ("Unknown type " ++ newTypeName)
    Just ntd -> typeToExpFams nts (expandNewType ntd params)
typeToExpFams _ other = error ("Cannot get exponential family for type: " ++ show other)

graphValueEmbeddedVars :: GraphValue -> [VarId]
graphValueEmbeddedVars UnitGraphValue = []
graphValueEmbeddedVars (VarGraphValue v) = [v]
graphValueEmbeddedVars (PairGraphValue a b) =
  graphValueEmbeddedVars a ++ graphValueEmbeddedVars b
graphValueEmbeddedVars (EitherGraphValue c a b) =
  [c] ++ graphValueEmbeddedVars a ++ graphValueEmbeddedVars b
graphValueEmbeddedVars (PureLeftGraphValue a) = graphValueEmbeddedVars a
graphValueEmbeddedVars (PureRightGraphValue a) = graphValueEmbeddedVars a
-- graphValueEmbeddedVars (MuGraphValue _ a) = graphValueEmbeddedVars a
graphValueEmbeddedVars (LambdaGraphValue _) =
  error "Cannot get embedded variables in LambdaGraphValue"

varsToGraphValue' :: Map String NewTypeDefinition -> TypeExpr -> State [VarId] GraphValue
varsToGraphValue' _ (ConstTExpr "_Unit") = return UnitGraphValue
varsToGraphValue' _ (ConstTExpr x) | elem x ["Bool", "Double"] = do
  (v:vs) <- get
  put vs
  return $ VarGraphValue v
varsToGraphValue' nts (AppTExpr (AppTExpr (ConstTExpr "_Pair") a) b) =
  PairGraphValue <$> varsToGraphValue' nts a <*> varsToGraphValue' nts b
varsToGraphValue' nts (AppTExpr (AppTExpr (ConstTExpr "_Either") a) b) = do
  (v:vs) <- get
  put vs
  EitherGraphValue v <$> varsToGraphValue' nts a <*> varsToGraphValue' nts b
varsToGraphValue' nts (splitAppType -> (ConstTExpr newTypeName, params)) =
  case Map.lookup newTypeName nts of
    Nothing -> error ("Unknown type " ++ newTypeName)
    Just ntd -> varsToGraphValue' nts (expandNewType ntd params)


varsToGraphValue' _ other =
  error ("Cannot get graph value for type: " ++ show other)

varsToGraphValue :: Map String NewTypeDefinition -> TypeExpr -> [VarId] -> GraphValue
varsToGraphValue nts t vars = case runState (varsToGraphValue' nts t) vars of
  (result, []) -> result
  other -> error $ "Too many variables (" ++ show (length vars) ++ ") for type " ++ show t

fmapNewtype :: TypeExpr -> String -> (GraphValue -> GraphBuilder Value GraphValue) -> GraphValue -> GraphBuilder Value GraphValue
fmapNewtype (VarTExpr var) v f val | var == v = f val
                                   | otherwise = return val
fmapNewtype (ConstTExpr _) _ _ val = return val
fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "_Pair") atype) btype) v f (PairGraphValue a b) =
  PairGraphValue <$> fmapNewtype atype v f a <*> fmapNewtype btype v f b
fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "_Either") ltype) rtype) v f (EitherGraphValue c l r) =
  EitherGraphValue c <$> fmapNewtype ltype v f l <*> fmapNewtype rtype v f r
fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "_Either") ltype) rtype) v f (PureLeftGraphValue l) =
  PureLeftGraphValue <$> fmapNewtype ltype v f l
fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "_Either") ltype) rtype) v f (PureRightGraphValue r) =
  PureRightGraphValue <$> fmapNewtype rtype v f r
fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "->") argtype) rettype) v f (LambdaGraphValue lam) =
  -- TODO: v should not appear in argtype
  return $ LambdaGraphValue $ \arg -> lam arg >>= fmapNewtype rettype v f

const2 = const . const

defaultContext :: Map String (Map String NewTypeDefinition -> GraphBuilder Value GraphValue)
defaultContext = Map.fromList [
  -- unify :: a -> a -> a
  -- conditions on its arguments being equal, returning one of them
  ("unify",
   const $ return $ LambdaGraphValue $ \v1 ->
     return $ LambdaGraphValue $ \v2 -> unifyGraphValues v1 v2),
  ("_unit", const $ return UnitGraphValue),
  ("_fst",
   const $ return $ LambdaGraphValue $ \(PairGraphValue first _) -> return first),
  ("_snd",
   const $ return $ LambdaGraphValue $ \(PairGraphValue _ second) -> return second),
  ("_pair",
   const $ return $ LambdaGraphValue $ \first -> return $ LambdaGraphValue $
     \second -> return $ PairGraphValue first second),
  ("_left",
   const $ return $ LambdaGraphValue $ \value -> return $ PureLeftGraphValue value),
  ("_right",
   const $ return $ LambdaGraphValue $ \value -> return $ PureRightGraphValue value),
  ("_either",
   let getResult (PureLeftGraphValue leftVal) leftHandler rightHandler = leftHandler leftVal
       getResult (PureRightGraphValue rightVal) leftHandler rightHandler = rightHandler rightVal
       getResult (EitherGraphValue isRightVar leftVal rightVal) leftHandler rightHandler = do
         leftResult <- leftHandler leftVal
         rightResult <- rightHandler rightVal
         ifThenElse isRightVar leftResult rightResult
       getResult other _ _ = error $ "Not an either: " ++ show other
   in const $ return $ LambdaGraphValue $ \eitherValue ->
     return $ LambdaGraphValue $ \(LambdaGraphValue leftHandler) ->
       return $ LambdaGraphValue $ \(LambdaGraphValue rightHandler) ->
         getResult eitherValue leftHandler rightHandler
  ),
  -- TODO: fix these values to return MuGraphValues
  ("mu",
  -- TODO: let you apply typegraphvalues!
  \nts -> return $ LambdaGraphValue $ \functorTypeValue -> case functorTypeValue of
    TypeGraphValue functorType ->
      case splitAppType functorType of
        (ConstTExpr functorName, _) -> case Map.lookup functorName nts of
          Nothing -> error ("No newtype " ++ functorName)
          Just def -> return $ LambdaGraphValue (return . MuGraphValue def)
        _ -> error $ "Not a valid functor: " ++ show functorType
    _ -> error $ "Mu argument is not a type: " ++ show functorTypeValue
  ),
  ("unMu",
   const $ return $ LambdaGraphValue $ \(MuGraphValue _ v) -> return v
  ),
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
   \nts ->
     return $ LambdaGraphValue $ \argTypeValue -> case argTypeValue of
       TypeGraphValue argType -> return $ LambdaGraphValue $ \resTypeValue -> case resTypeValue of
         TypeGraphValue resType -> do
           let argExpFams = typeToExpFams nts argType
               resExpFams = typeToExpFams nts resType
           rfs <- mapM (flip newRandFun argExpFams) resExpFams
           return $ LambdaGraphValue $ \argValue -> do
             let argVars = graphValueEmbeddedVars argValue
             resVars <- mapM (flip newSampleFromRandFun argVars) rfs
             return $ varsToGraphValue nts resType resVars
         other -> error $ "randFunction called with non-type second argument " ++ show other
       other -> error $ "randFunction called with non-type first argument " ++ show other
  )
  ]
