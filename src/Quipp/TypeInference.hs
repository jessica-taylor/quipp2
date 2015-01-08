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
data Expr = VarExpr String | WithTypeExpr Expr TypeExpr | LambdaExpr String Expr | AppExpr Expr Expr | DefExpr String Expr Expr | LiteralExpr Value | NewTypeExpr NewTypeDefinition Expr deriving (Eq, Ord)

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
  showsPrec p (DefExpr s v b) =
    showParen (p > 1) $ showString "def " . showString s . showString " = " . showsPrec 0 v . showString ";\n" . showsPrec 0 b
  showsPrec p (NewTypeExpr (name, params, inner) body) =
    showParen (p > 1) $ showString "newtype " . showString (unwords (name : params)) . showString " = " . showsPrec 0 inner . showString ";\n" . showsPrec 0 body

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

reduceTypeShallow :: TypeExpr -> TypeCheck TypeExpr
reduceTypeShallow t = do
  (m, _) <- lift get
  return (reduceTypeShallowIn m t)

reduceTypeDeepIn :: Map String TypeExpr -> TypeExpr -> TypeExpr
reduceTypeDeepIn m t = case reduceTypeShallowIn m t of
  AppTExpr fun arg -> AppTExpr (reduceTypeDeepIn m fun) (reduceTypeDeepIn m arg)
  other -> other

reduceTypeDeep :: TypeExpr -> TypeCheck TypeExpr
reduceTypeDeep t = do
  (m, _) <- lift get
  return (reduceTypeDeepIn m t)


simpleValueType :: Value -> TypeExpr
simpleValueType (DoubleValue _) = ConstTExpr "Double"
simpleValueType (BoolValue _) = ConstTExpr "Bool"

-- We can't get the type of an arbitrary GraphValue.  However, we can do some
-- sanity checks to make sure it's not completely the wrong type.


-- perhaps the rest should be split up?
--


data GraphValue = VarGraphValue VarId | LambdaGraphValue (GraphValue -> GraphBuilder Value GraphValue) | UnitGraphValue | PairGraphValue GraphValue GraphValue | EitherGraphValue VarId GraphValue GraphValue | PureLeftGraphValue GraphValue | PureRightGraphValue GraphValue | MuGraphValue NewTypeDefinition GraphValue | TypeGraphValue TypeExpr

data FrozenGraphValue = FValueGraphValue Value | FUnitGraphValue | FPairGraphValue FrozenGraphValue FrozenGraphValue | FLeftGraphValue FrozenGraphValue | FRightGraphValue FrozenGraphValue | FMuGraphValue NewTypeDefinition FrozenGraphValue | FTypeGraphValue TypeExpr deriving (Eq, Ord)

instance Show GraphValue where
  show (VarGraphValue varid) = "$" ++ show varid
  show (LambdaGraphValue _) = "#lambda"
  show UnitGraphValue = "()"
  show (PairGraphValue a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (EitherGraphValue varid left right) = "if " ++ show varid ++ " then Left " ++ show left ++ " else Right " ++ show right
  show (PureLeftGraphValue left) = "(Left " ++ show left ++ ")"
  show (PureRightGraphValue right) = "(Right " ++ show right ++ ")"
  show (MuGraphValue _ v) = "(Mu " ++ show v ++ ")"
  show (TypeGraphValue t) = show t

instance Show FrozenGraphValue where
  show (FValueGraphValue v) = show v
  show FUnitGraphValue = "()"
  show (FPairGraphValue a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (FLeftGraphValue a) = "(Left " ++ show a ++ ")"
  show (FRightGraphValue b) = "(Right " ++ show b ++ ")"
  show (FMuGraphValue _ v) = "(Mu " ++ show v ++ ")"
  show (FTypeGraphValue t) = show t

freezeGraphValue :: (VarId -> Value) -> GraphValue -> FrozenGraphValue
freezeGraphValue _ UnitGraphValue = FUnitGraphValue
freezeGraphValue f (VarGraphValue v) = FValueGraphValue $ f v
freezeGraphValue f (PairGraphValue a b) = FPairGraphValue (freezeGraphValue f a) (freezeGraphValue f b)
freezeGraphValue f (EitherGraphValue c l r) = case f c of
  BoolValue False -> FLeftGraphValue (freezeGraphValue f l)
  BoolValue True -> FRightGraphValue (freezeGraphValue f r)
  other -> error ("Bad boolean: " ++ show other)
freezeGraphValue f (PureLeftGraphValue l) = FLeftGraphValue (freezeGraphValue f l)
freezeGraphValue f (PureRightGraphValue r) = FRightGraphValue (freezeGraphValue f r)
freezeGraphValue f (MuGraphValue def v) = FMuGraphValue def (freezeGraphValue f v)
freezeGraphValue _ other = error "Cannot freeze lambdas"
freezeGraphValue _ (TypeGraphValue t) = FTypeGraphValue t

unfreezeGraphValue :: FrozenGraphValue -> GraphBuilder Value GraphValue
unfreezeGraphValue FUnitGraphValue = return UnitGraphValue
unfreezeGraphValue (FValueGraphValue value) =
  VarGraphValue <$> constValue (expFamForType (simpleValueType value)) value
unfreezeGraphValue (FPairGraphValue a b) =
  PairGraphValue <$> unfreezeGraphValue a <*> unfreezeGraphValue b
unfreezeGraphValue (FLeftGraphValue value) = PureLeftGraphValue <$> unfreezeGraphValue value
unfreezeGraphValue (FRightGraphValue value) = PureRightGraphValue <$> unfreezeGraphValue value
unfreezeGraphValue (FMuGraphValue def v) = MuGraphValue def <$> unfreezeGraphValue  v
unfreezeGraphValue other = error ("Cannot freeze " ++ show other)
unfreezeGraphValue (FTypeGraphValue t) = return $ TypeGraphValue t

expFamForType :: TypeExpr -> ExpFam Value
expFamForType (ConstTExpr "Double") = gaussianValueExpFam
expFamForType (ConstTExpr "Bool") = boolValueExpFam
expFamForType t = error $ "Can't get exponential family for type " ++ show t

multiArgFunction :: Int -> ([GraphValue] -> GraphBuilder GraphValue) -> GraphBuilder GraphValue
multiArgFunction 0 fn = fn []
multiArgFunction nArgs fn = LambdaGraphValue $ \firstArg -> multiArgFunction (nArgs - 1) (\restArgs -> fn (firstArg : restArgs))

expandNewType :: NewTypeDefinition -> [TypeExpr] -> TypeExpr
expandNewType (_, paramVars, inner) params =
  reduceTypeDeepIn (foldr (uncurry Map.insert) Map.empty (zipSameLength paramVars params)) inner


-- interpretPattern :: PatternExpr -> GraphValue -> GraphBuilder Value (Maybe [(String, GraphValue)])
-- interpretPattern (VarPExpr var) value = return $ Just [(var, value)]
-- interpretPattern (ConstrPExpr constr 

interpretExpr :: Map String (Map String NewTypeDefinition -> GraphBuilder Value GraphValue) -> Map String NewTypeDefinition -> AnnotatedExpr -> GraphBuilder Value GraphValue

interpretExpr _ _ x | trace ("\ninterpret " ++ show x) False = undefined

interpretExpr m nts (typ, VarAExpr var) = case Map.lookup var m of
  Nothing -> error ("cannot find variable " ++ var)
  Just val -> val typ nts

interpretExpr m nts (_, LambdaAExpr param _ body) = return $ LambdaGraphValue $
  \arg -> interpretExpr (Map.insert param (const2 $ return arg) m) nts body

interpretExpr m nts (_, AppAExpr fun arg) = do
  funVal <- interpretExpr m nts fun
  case funVal of
    LambdaGraphValue f -> interpretExpr m nts arg >>= f
    _ -> error "Function in application expression is not actually a function"

interpretExpr m nts (_, DefAExpr var (_, value) body) = do
  interpretExpr (Map.insert var (\t _ -> trace ("\nTTT: " ++ show t) $ interpretExpr m nts (t, value)) m) nts body

interpretExpr m nts (t, LiteralAExpr value) = do
  var <- newVar (expFamForType t)
  newConstFactor var value
  return $ VarGraphValue var

interpretExpr m nts (_, NewTypeAExpr defn@(typeName, typeArgs, innerType) body) = do
  let wrappedType = foldl AppTExpr (ConstTExpr typeName) (map VarTExpr typeArgs)
  let idFun = const $ return $ LambdaGraphValue $ \x -> return x
  let valueToType (TypeGraphValue t) = t
  typeConstr <- multiArgFunction (length typeArgs) (\typeArgVals -> return $ expandNewType defn (map valueToType typeArgVals))
  interpretExpr (Map.insert ("Make" ++ typeName) idFun $ Map.insert ("un" ++ typeName) idFun $ Map.insert typeName typeConstr m) (Map.insert typeName defn nts) body

notVar :: VarId -> GraphBuilder Value VarId
notVar x = do
  y <- newVar boolValueExpFam
  newFactor notFactor [y, x]
  return y

ifThenElse _ UnitGraphValue UnitGraphValue = return UnitGraphValue

ifThenElse pvar (PairGraphValue a b) (PairGraphValue c d) = do
  first <- ifThenElse pvar a c
  second <- ifThenElse pvar b d
  return $ PairGraphValue first second

ifThenElse pvar (EitherGraphValue p1 a b) (EitherGraphValue p2 c d) = do
  VarGraphValue p' <- ifThenElse pvar (VarGraphValue p1) (VarGraphValue p2)
  left <- ifThenElse pvar a c
  right <- ifThenElse pvar b d
  return $ EitherGraphValue p' left right

ifThenElse pvar (PureLeftGraphValue a) (PureLeftGraphValue b) =
  PureLeftGraphValue <$> ifThenElse pvar a b

ifThenElse pvar (PureRightGraphValue a) (PureRightGraphValue b) =
  PureRightGraphValue <$> ifThenElse pvar a b

ifThenElse pvar (PureLeftGraphValue a) (PureRightGraphValue b) =
  return $ EitherGraphValue pvar a b

ifThenElse pvar (PureRightGraphValue a) (PureLeftGraphValue b) =
  EitherGraphValue <$> notVar pvar <*> return a <*> return b

ifThenElse pvar (PureLeftGraphValue a) (EitherGraphValue p b c) = do
  leftp <- constValue boolValueExpFam (BoolValue False)
  VarGraphValue p' <- ifThenElse pvar (VarGraphValue leftp) (VarGraphValue p)
  EitherGraphValue p' <$> ifThenElse pvar a b <*> return c

ifThenElse pvar e@(EitherGraphValue _ _ _) l@(PureLeftGraphValue _) = do
  pvar' <- notVar pvar
  ifThenElse pvar' l e

ifThenElse pvar (PureRightGraphValue a) (EitherGraphValue p b c) = do
  rightp <- constValue boolValueExpFam (BoolValue True)
  VarGraphValue p' <- ifThenElse pvar (VarGraphValue rightp) (VarGraphValue p)
  EitherGraphValue p' b <$> ifThenElse pvar a c

ifThenElse pvar e@(EitherGraphValue _ _ _) r@(PureRightGraphValue _) = do
  pvar' <- notVar pvar
  ifThenElse pvar' r e

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

ifThenElse pvar (MuGraphValue d1 v1) (MuGraphValue d2 v2)
  | d1 == d2 = MuGraphValue d1 <$> ifThenElse pvar v1 v2
  | otherwise = error "Mu definitions do not match"

unifyGraphValues :: GraphValue -> GraphValue -> GraphBuilder Value GraphValue
unifyGraphValues (VarGraphValue a) (VarGraphValue b) = liftM VarGraphValue $ conditionEqual a b
unifyGraphValues (PairGraphValue a b) (PairGraphValue c d) =
  PairGraphValue <$> unifyGraphValues a c <*> unifyGraphValues b d
unifyGraphValues (EitherGraphValue a b c) (EitherGraphValue d e f) =
  EitherGraphValue <$> conditionEqual a d <*> unifyGraphValues b e <*> unifyGraphValues c f
unifyGraphValues (PureLeftGraphValue a) (PureLeftGraphValue b) =
  unifyGraphValues a b
unifyGraphValues (PureRightGraphValue a) (PureRightGraphValue b) =
  unifyGraphValues a b
unifyGraphValues (PureLeftGraphValue a) (EitherGraphValue b c d) = do
  newConstFactor b (BoolValue False)
  unifyGraphValues a c
unifyGraphValues (PureRightGraphValue a) (EitherGraphValue b c d) = do
  newConstFactor b (BoolValue True)
  unifyGraphValues a d
unifyGraphValues a@(EitherGraphValue _ _ _) b@(PureLeftGraphValue _) =
  unifyGraphValues b a
unifyGraphValues a@(EitherGraphValue _ _ _) b@(PureRightGraphValue _) =
  unifyGraphValues b a
unifyGraphValues UnitGraphValue UnitGraphValue = return UnitGraphValue
unifyGraphValues (MuGraphValue _ v1) (MuGraphValue _ v2) = unifyGraphValues v1 v2
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
defaultContext = Map.fromList $ map (\(a, b, c) -> (a, (b >>= cloneWithNewVars, c))) [
  -- unify :: a -> a -> a
  -- conditions on its arguments being equal, returning one of them
  ("unify",
   const $ return $ LambdaGraphValue $ \v1 ->
     return $ LambdaGraphValue $ \v2 -> unifyGraphValues v1 v2),
  ("_unit", return (ConstTExpr "_Unit"), const2 $ return UnitGraphValue),
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
   in const $ return $ LambdaGraphValue $ \eitherValue ->
     return $ LambdaGraphValue $ \(LambdaGraphValue leftHandler) ->
       return $ LambdaGraphValue $ \(LambdaGraphValue rightHandler) ->
         getResult eitherValue leftHandler rightHandler
  ),
  -- TODO: fix these values to return MuGraphValues
  -- ("mu",
  --  const $ return $ LambdaGraphValue $ \resultType ->
  --  \thisType -> case thisType of
  --    (AppTExpr (AppTExpr (ConstTExpr "->") (AppTExpr functorType _)) _) ->
  --      case splitAppType functorType of
  --        (ConstTExpr functorName, _) ->
  --         \nts -> case Map.lookup functorName nts of
  --                   Nothing -> error ("No newtype " ++ functorName)
  --                   Just def -> return $ LambdaGraphValue (return . MuGraphValue def)
  --        _ -> error ("Mu cannot have type " ++ show thisType)
  --    _ -> error ("Mu cannot have type " ++ show thisType)
  -- ),
  -- ("unMu",
  --  do f <- newVarType "unMu_f"
  --     return $ functionType (muType f) (AppTExpr f (muType f)),
  --  const2 $ return $ LambdaGraphValue $ \(MuGraphValue _ v) -> return v
  -- ),
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
  -- TODO: somehow this has to be lazy.  See what it's called with, then
  -- make a different function for each?  Or just take arg type as an argument.
  ("randFunction",
   \nts ->
     return $ LambdaGraphValue $ \(TypeGraphValue argType) ->
       return $ LambdaGraphValue $ \(TypeGraphValue resType) -> do
         let argExpFams = typeToExpFams nts argType
             resExpFams = typeToExpFams nts resType
         rfs <- mapM (flip newRandFun argExpFams) resExpFams
         return $ LambdaGraphValue $ \argValue -> do
           let argVars = graphValueEmbeddedVars argValue
           resVars <- mapM (flip newSampleFromRandFun argVars) rfs
           return $ varsToGraphValue nts resType resVars)
  ]
