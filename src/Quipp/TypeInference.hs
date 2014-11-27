{-# LANGUAGE TupleSections #-}

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

data TypeExpr = VarTExpr String | ConstTExpr String | AppTExpr TypeExpr TypeExpr deriving (Eq, Ord)

instance Show TypeExpr where
  showsPrec _ (VarTExpr v) = showString v
  showsPrec _ (ConstTExpr s) = showString s
  showsPrec p (AppTExpr (AppTExpr (ConstTExpr "->") a) r) =
    showParen (p > 5) $ showsPrec 6 a . showString " -> " . showsPrec 5 r
  showsPrec p (AppTExpr a b) =
    showParen (p > 10) $ showsPrec 10 a . showString " " . showsPrec 11 b

type NewTypeDefinition = (String, [String], TypeExpr)

-- Expressions annotated by type.
data AnnotatedExprBody = VarAExpr String | LambdaAExpr String TypeExpr AnnotatedExpr | AppAExpr AnnotatedExpr AnnotatedExpr | DefAExpr String AnnotatedExpr AnnotatedExpr | LiteralAExpr Value | NewTypeAExpr NewTypeDefinition AnnotatedExpr deriving (Eq, Ord, Show)

type AnnotatedExpr = (TypeExpr, AnnotatedExprBody)

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

type HindleyMilnerState = (Map String TypeExpr, TypeId)

type TypeCheck = ReaderT [String] (StateT HindleyMilnerState (Either String))

functionType a b = AppTExpr (AppTExpr (ConstTExpr "->") a) b
pairType a b = AppTExpr (AppTExpr (ConstTExpr "Pair") a) b
eitherType a b = AppTExpr (AppTExpr (ConstTExpr "Either") a) b
muType f = AppTExpr (ConstTExpr "Mu") f

newTypeId :: String -> TypeCheck String
newTypeId str = do
  (m, tid) <- lift get
  lift $ put (m, tid + 1)
  return ("_" ++ str ++ "_" ++ show tid)

typeError :: String -> TypeCheck a
typeError s = do
  stack <- ask 
  lift $ lift $ Left $ "At\n" ++ (reverse stack >>= (++ "\n\n")) ++ ": " ++ s

pushTypeCheckStack :: String -> TypeCheck a -> TypeCheck a
pushTypeCheckStack s = local (s:)

newVarType = liftM VarTExpr . newTypeId

reduceTypeShallow :: TypeExpr -> TypeCheck TypeExpr
reduceTypeShallow t@(VarTExpr v) = do
  (m, _) <- lift get
  case Map.lookup v m of
    Nothing -> return t
    Just t' -> reduceTypeShallow t'
reduceTypeShallow other = return other

reduceTypeDeep :: TypeExpr -> TypeCheck TypeExpr
reduceTypeDeep t = do
  t' <- reduceTypeShallow t
  case t' of
    AppTExpr fun arg -> AppTExpr <$> reduceTypeDeep fun <*> reduceTypeDeep arg
    other -> return other

reduceTypesInAnnotatedExpr :: AnnotatedExpr -> TypeCheck AnnotatedExpr
reduceTypesInAnnotatedExpr (t, abody) = do
  t' <- reduceTypeDeep t
  abody' <- case abody of
    VarAExpr _ -> return abody
    LiteralAExpr _ -> return abody
    LambdaAExpr param typ body ->
      LambdaAExpr param <$> reduceTypeDeep typ <*> reduceTypesInAnnotatedExpr body
    AppAExpr fun arg -> AppAExpr <$> reduceTypesInAnnotatedExpr fun <*> reduceTypesInAnnotatedExpr arg
    DefAExpr var value body -> DefAExpr var <$> reduceTypesInAnnotatedExpr value <*> reduceTypesInAnnotatedExpr body
    NewTypeAExpr def body -> NewTypeAExpr def <$> reduceTypesInAnnotatedExpr body
  return (t', abody')

varOccursInReduced :: String -> TypeExpr -> TypeCheck Bool
varOccursInReduced v (VarTExpr v') = return $ v == v'
varOccursInReduced v (AppTExpr a b) = do 
  aocc <- varOccursIn v a
  if aocc then return True else varOccursIn v b
varOccursInReduced v other = return False

varOccursIn v x = reduceTypeShallow x >>= varOccursInReduced v

unifyReduced :: TypeExpr -> TypeExpr -> TypeCheck ()

unifyReduced (VarTExpr v) other
  | VarTExpr v == other = return ()
  | otherwise = do
    occurs <- varOccursIn v other
    if occurs && other /= VarTExpr v then typeError ("Occurs check failed: " ++ v ++ " unified with " ++ show other)
    else do
      (m, count) <- lift get
      lift $ put (Map.insert v other m, count)

unifyReduced other t@(VarTExpr v) = unifyReduced t other

unifyReduced (ConstTExpr a) (ConstTExpr b) | a == b = return ()

unifyReduced (AppTExpr a b) (AppTExpr c d) = do
  unify a c
  unify b d

unifyReduced a b = typeError $ "Unification failed: " ++ show a ++ ", " ++ show b

unify :: TypeExpr -> TypeExpr -> TypeCheck ()

unify a b = do
  -- a' <- reduceTypeShallow a
  -- b' <- reduceTypeShallow b
  a' <- reduceTypeDeep a
  b' <- reduceTypeDeep b
  pushTypeCheckStack ("unify " ++ show a' ++ ", " ++ show b') $ unifyReduced a' b'


cloneWithNewVarsReduced :: Map String String -> TypeExpr -> TypeCheck (TypeExpr, Map String String)

cloneWithNewVarsReduced m (VarTExpr v) = case Map.lookup v m of
  Just newvar -> return (VarTExpr newvar, m)
  Nothing -> do
    newvar <- newTypeId v
    return (VarTExpr newvar, Map.insert v newvar m)

cloneWithNewVarsReduced m (AppTExpr fun arg) = do
  (funType, m') <- cloneWithNewVars' m fun
  (argType, m'') <- cloneWithNewVars' m' arg
  return (AppTExpr funType argType, m'')

cloneWithNewVarsReduced m other = return (other, m)

cloneWithNewVars' :: Map String String -> TypeExpr -> TypeCheck (TypeExpr, Map String String)
cloneWithNewVars' m t = do
  t' <- reduceTypeShallow t
  cloneWithNewVarsReduced m t'

cloneWithNewVars :: TypeExpr -> TypeCheck TypeExpr
cloneWithNewVars = liftM fst . cloneWithNewVars' Map.empty


type HindleyMilnerContext = (Map String (TypeCheck TypeExpr), Map String TypeExpr)

splitFunctionType :: TypeExpr -> ([TypeExpr], TypeExpr)
splitFunctionType (AppTExpr (AppTExpr (ConstTExpr "->") a) b) =
  let (args, res) = splitFunctionType b in (a:args, res)
splitFunctionType other = ([], other)


-- hindleyMilnerPattern :: HindleyMilnerContext -> PatternExpr -> TypeExpr -> TypeCheck [(String, TypeExpr)]
-- 
-- hindleyMilnerPattern _ (VarPExpr var) t = return [(var, t)]
-- 
-- hindleyMilnerPattern ctx@(varctx, typectx) (ConstrPExpr constr fields) t =
--   case Map.lookup constr varctx of
--     Nothing -> lift (Left $ "Unknown constructor " ++ constr)
--     Just getConstrType -> do
--       constrType <- getConstrType
--       let (argTypes, resType) = splitFunctionType constrType
--       unify t resType
--       if length argTypes /= length fields
--       then error "Wrong number of fields in pattern"
--       else do
--         substs <- zipWithM (hindleyMilnerPattern ctx) fields argTypes
--         return $ concat substs

simpleValueType :: Value -> TypeExpr
simpleValueType (DoubleValue _) = ConstTExpr "Double"
simpleValueType (BoolValue _) = ConstTExpr "Bool"

hindleyMilner :: HindleyMilnerContext -> Expr -> TypeCheck AnnotatedExpr

-- hindleyMilner _ x | traceShow x False = undefined
hindleyMilner ctx x = pushTypeCheckStack ("hindleyMilner " ++ show x ++ " # " ++ show (Map.keys $ fst ctx)) $ hindleyMilner' ctx x

hindleyMilner' :: HindleyMilnerContext -> Expr -> TypeCheck AnnotatedExpr

hindleyMilner' (vars, _) (VarExpr v) = case Map.lookup v vars of
  Nothing -> typeError $ "Unknown variable " ++ show v
  Just getT -> do
    t <- getT
    return (t, VarAExpr v)

hindleyMilner' ctx (WithTypeExpr expr typ) = do
  aexpr@(exprType, _) <- hindleyMilner ctx expr
  unify exprType typ
  return aexpr

hindleyMilner' (varctx, typectx) (LambdaExpr var body) = do
  argType <- newVarType "lambda_arg"
  bodyAExpr@(bodyType, _) <- hindleyMilner (Map.insert var (return argType) varctx, typectx) body
  return (functionType argType bodyType, LambdaAExpr var argType bodyAExpr)

hindleyMilner' ctx (AppExpr fun arg) = do
  funAExpr@(funType, _) <- hindleyMilner ctx fun
  argAExpr@(argType, _) <- hindleyMilner ctx arg
  funType' <- reduceTypeDeep funType
  argType' <- reduceTypeDeep argType
  pushTypeCheckStack ("in application, " ++ show fun ++ " : " ++ show funType' ++ " **and** " ++ show arg ++ " : " ++ show argType') $ do
    resultType <- newVarType "app_result"
    unify funType' (functionType argType' resultType)
    return (resultType, AppAExpr funAExpr argAExpr)

hindleyMilner' ctx@(varctx, typectx) (DefExpr var value body) = do
  valueAExpr@(valueType, _) <- hindleyMilner ctx value
  bodyAExpr@(bodyType, _) <- hindleyMilner (Map.insert var (cloneWithNewVars valueType) varctx, typectx) body
  return (bodyType, DefAExpr var valueAExpr bodyAExpr)

hindleyMilner' ctx (LiteralExpr lit) = return (simpleValueType lit, LiteralAExpr lit)

hindleyMilner' (varctx, typectx) (NewTypeExpr defn@(typeName, typeArgs, innerType) body) =
  -- TODO: must be functor?
  let wrappedType = foldl AppTExpr (ConstTExpr typeName) (map VarTExpr typeArgs)
      varctx' = Map.insert typeName (cloneWithNewVars $ functionType innerType wrappedType) varctx
      varctx'' = Map.insert ("un" ++ typeName) (cloneWithNewVars $ functionType wrappedType innerType) varctx'
      idFun t u = (functionType t u, LambdaAExpr "a" t (u, VarAExpr "b"))
  in do
    bodyAExpr@(bodyType, _) <- hindleyMilner (varctx'', typectx) body
    return (bodyType, NewTypeAExpr defn bodyAExpr)

typeInfer :: HindleyMilnerContext -> Expr -> Either String AnnotatedExpr
typeInfer ctx expr = case runStateT (runReaderT (hindleyMilner ctx expr >>= reduceTypesInAnnotatedExpr) []) (Map.empty, 0) of
  Left err -> Left err
  Right (ex, state) -> Right ex


-- perhaps the rest should be split up?

data GraphValue = VarGraphValue VarId | LambdaGraphValue (GraphValue -> GraphBuilder Value GraphValue) | UnitGraphValue | PairGraphValue GraphValue GraphValue | EitherGraphValue VarId GraphValue GraphValue | PureLeftGraphValue GraphValue | PureRightGraphValue GraphValue | MuGraphValue NewTypeDefinition GraphValue

data FrozenGraphValue = FValueGraphValue Value | FUnitGraphValue | FPairGraphValue FrozenGraphValue FrozenGraphValue | FLeftGraphValue FrozenGraphValue | FRightGraphValue FrozenGraphValue | FMuGraphValue NewTypeDefinition FrozenGraphValue deriving (Eq, Ord)

instance Show GraphValue where
  show (VarGraphValue varid) = "$" ++ show varid
  show (LambdaGraphValue _) = "#lambda"
  show UnitGraphValue = "()"
  show (PairGraphValue a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (EitherGraphValue varid left right) = "if " ++ show varid ++ " then Left " ++ show left ++ " else Right " ++ show right
  show (PureLeftGraphValue left) = "(Left " ++ show left ++ ")"
  show (PureRightGraphValue right) = "(Right " ++ show right ++ ")"
  show (MuGraphValue _ v) = "(Mu " ++ show v ++ ")"

instance Show FrozenGraphValue where
  show (FValueGraphValue v) = show v
  show FUnitGraphValue = "()"
  show (FPairGraphValue a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (FLeftGraphValue a) = "(Left " ++ show a ++ ")"
  show (FRightGraphValue b) = "(Right " ++ show b ++ ")"
  show (FMuGraphValue _ v) = "(Mu " ++ show v ++ ")"

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

-- unfreezeGraphValue :: TypeExpr -> FrozenGraphValue -> GraphBuilder Value GraphValue
-- unfreezeGraphValue _ FUnitGraphValue = return UnitGraphValue
-- unfreezeGraphValue t (FValueGraphValue value) = 
--   trace ("t " ++ show t ++ " value " ++ show value) $ VarGraphValue <$> constValue (expFamForType t) value
-- unfreezeGraphValue (AppTExpr (AppTExpr (ConstTExpr "Pair") firstType) secondType) (FPairGraphValue a b) =
--   trace ("pair " ++ show firstType ++ ";" ++ show secondType ++ "#" ++ show a ++ ";" ++ show b)
--   PairGraphValue <$> unfreezeGraphValue firstType a <*> unfreezeGraphValue secondType b
-- unfreezeGraphValue
--   (AppTExpr (AppTExpr (ConstTExpr "Either") leftType) rightType)
--   (FLeftGraphValue value) = PureLeftGraphValue <$> unfreezeGraphValue leftType value
-- unfreezeGraphValue
--   (AppTExpr (AppTExpr (ConstTExpr "Either") leftType) rightType)
--   (FRightGraphValue value) = PureRightGraphValue <$> unfreezeGraphValue rightType value
-- unfreezeGraphValue (AppTExpr (ConstTExpr "Mu") functorType) (FMuGraphValue def v) =
--   MuGraphValue def <$> unfreezeGraphValue (AppTExpr functorType (muType functorType)) v
-- unfreezeGraphValue t other = error ("Cannot freeze " ++ show other ++ " : " ++ show t)

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

expFamForType :: TypeExpr -> ExpFam Value
expFamForType (ConstTExpr "Double") = gaussianValueExpFam
expFamForType (ConstTExpr "Bool") = boolValueExpFam
expFamForType t = error $ "Can't get exponential family for type " ++ show t

-- interpretPattern :: PatternExpr -> GraphValue -> GraphBuilder Value (Maybe [(String, GraphValue)])
-- interpretPattern (VarPExpr var) value = return $ Just [(var, value)]
-- interpretPattern (ConstrPExpr constr 

interpretExpr :: Map String (TypeExpr -> Map String NewTypeDefinition -> GraphBuilder Value GraphValue) -> Map String NewTypeDefinition -> AnnotatedExpr -> GraphBuilder Value GraphValue

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
  let idFun = const2 $ return $ LambdaGraphValue $ \x -> return x
  interpretExpr (Map.insert typeName idFun $ Map.insert ("un" ++ typeName) idFun m) (Map.insert typeName defn nts) body

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
unifyGraphValues _ _ = error ("Cannot unify functions")


typeToExpFams :: TypeExpr -> [ExpFam Value]
typeToExpFams (ConstTExpr "Unit") = []
typeToExpFams t@(ConstTExpr _) = [expFamForType t]
typeToExpFams (AppTExpr (AppTExpr (ConstTExpr "Pair") a) b) =
  typeToExpFams a ++ typeToExpFams b
typeToExpFams (AppTExpr (AppTExpr (ConstTExpr "Either") a) b) =
  [boolValueExpFam] ++ typeToExpFams a ++ typeToExpFams b
typeToExpFams other = error ("Cannot get exponential family for type: " ++ show other)

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

varsToGraphValue' :: TypeExpr -> State [VarId] GraphValue
varsToGraphValue' (ConstTExpr "Unit") = return UnitGraphValue
varsToGraphValue' (ConstTExpr x) | elem x ["Bool", "Double"] = do
  (v:vs) <- get
  put vs
  return $ VarGraphValue v
varsToGraphValue' (AppTExpr (AppTExpr (ConstTExpr "Pair") a) b) =
  PairGraphValue <$> varsToGraphValue' a <*> varsToGraphValue' b
varsToGraphValue' (AppTExpr (AppTExpr (ConstTExpr "Either") a) b) = do
  (v:vs) <- get
  put vs
  EitherGraphValue v <$> varsToGraphValue' a <*> varsToGraphValue' b
varsToGraphValue' other =
  error ("Cannot get graph value for type: " ++ show other)

varsToGraphValue :: TypeExpr -> [VarId] -> GraphValue
varsToGraphValue t vars = case runState (varsToGraphValue' t) vars of
  (result, []) -> result
  other -> error $ "Too many variables (" ++ show (length vars) ++ ") for type " ++ show t

fmapNewtype :: TypeExpr -> String -> (GraphValue -> GraphBuilder Value GraphValue) -> GraphValue -> GraphBuilder Value GraphValue
fmapNewtype (VarTExpr var) v f val | var == v = f val
                                   | otherwise = return val
fmapNewtype (ConstTExpr _) _ _ val = return val
fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "Pair") atype) btype) v f (PairGraphValue a b) =
  PairGraphValue <$> fmapNewtype atype v f a <*> fmapNewtype btype v f b
fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "Either") ltype) rtype) v f (EitherGraphValue c l r) =
  EitherGraphValue c <$> fmapNewtype ltype v f l <*> fmapNewtype rtype v f r
fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "Either") ltype) rtype) v f (PureLeftGraphValue l) =
  PureLeftGraphValue <$> fmapNewtype ltype v f l
fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "Either") ltype) rtype) v f (PureRightGraphValue r) =
  PureRightGraphValue <$> fmapNewtype rtype v f r
fmapNewtype (AppTExpr (AppTExpr (ConstTExpr "->") argtype) rettype) v f (LambdaGraphValue lam) =
  -- TODO: v should not appear in argtype
  return $ LambdaGraphValue $ \arg -> lam arg >>= fmapNewtype rettype v f

const2 = const . const

defaultContext :: Map String (TypeCheck TypeExpr, TypeExpr -> Map String NewTypeDefinition -> GraphBuilder Value GraphValue)
defaultContext = Map.fromList $ map (\(a, b, c) -> (a, (b >>= cloneWithNewVars, c))) [
  -- unify :: a -> a -> a
  -- conditions on its arguments being equal, returning one of them
  ("unify",
   do a <- newVarType "unify_type"
      return $ functionType a $ functionType a a,
   const2 $ return $ LambdaGraphValue $ \v1 ->
     return $ LambdaGraphValue $ \v2 -> unifyGraphValues v1 v2),
  ("unit", return (ConstTExpr "Unit"), const2 $ return UnitGraphValue),
  ("fst",
   do a <- newVarType "pair_fst"
      b <- newVarType "pair_snd"
      return $ functionType (pairType a b) a,
   const2 $ return $ LambdaGraphValue $ \(PairGraphValue first _) -> return first),
  ("snd",
   do a <- newVarType "pair_fst"
      b <- newVarType "pair_snd"
      return $ functionType (pairType a b) b,
   const2 $ return $ LambdaGraphValue $ \(PairGraphValue _ second) -> return second),
  ("pair",
   do a <- newVarType "pair_fst"
      b <- newVarType "pair_snd"
      return $ functionType a $ functionType b $ pairType a b,
   const2 $ return $ LambdaGraphValue $ \first -> return $ LambdaGraphValue $
     \second -> return $ PairGraphValue first second),
  ("left",
   do a <- newVarType "either_left"
      b <- newVarType "either_right"
      return $ functionType a $ eitherType a b,
   const2 $ return $ LambdaGraphValue $ \value -> return $ PureLeftGraphValue value),
  ("right",
   do a <- newVarType "either_left"
      b <- newVarType "either_right"
      return $ functionType b $ eitherType a b,
   const2 $ return $ LambdaGraphValue $ \value -> return $ PureRightGraphValue value),
  ("either",
   do a <- newVarType "either_left"
      b <- newVarType "either_right"
      c <- newVarType "either_res"
      return $ functionType (eitherType a b) $ functionType (functionType a c) $ functionType (functionType b c) c,
   let getResult (PureLeftGraphValue leftVal) leftHandler rightHandler = leftHandler leftVal
       getResult (PureRightGraphValue rightVal) leftHandler rightHandler = rightHandler rightVal
       getResult (EitherGraphValue isRightVar leftVal rightVal) leftHandler rightHandler = do
         leftResult <- leftHandler leftVal
         rightResult <- rightHandler rightVal
         ifThenElse isRightVar leftResult rightResult
   in const2 $ return $ LambdaGraphValue $ \eitherValue ->
     return $ LambdaGraphValue $ \(LambdaGraphValue leftHandler) ->
       return $ LambdaGraphValue $ \(LambdaGraphValue rightHandler) ->
         getResult eitherValue leftHandler rightHandler
  ),
  -- TODO: fix these values to return MuGraphValues
  ("mu",
   do f <- newVarType "mu_f"
      return $ functionType (AppTExpr f (muType f)) (muType f),
   \thisType -> case thisType of
     (AppTExpr (AppTExpr (ConstTExpr "->") (AppTExpr functorType _)) _) ->
       let typeHead (ConstTExpr t) = t
           typeHead (AppTExpr t _) = typeHead t
           typeHead other = error ("Mu cannot have type " ++ show thisType)
           functorName = typeHead functorType
       in \nts -> case Map.lookup functorName nts of
                    Nothing -> error ("No newtype " ++ functorName)
                    Just def -> return $ LambdaGraphValue (return . MuGraphValue def)
     _ -> error ("Mu cannot have type " ++ show thisType)
  ),
  ("unMu",
   do f <- newVarType "unMu_f"
      return $ functionType (muType f) (AppTExpr f (muType f)),
   const2 $ return $ LambdaGraphValue $ \(MuGraphValue _ v) -> return v
  ),
  -- cata :: Functor f => (f a -> a) -> Mu f -> a
  -- cata f = f . fmap (cata f) . unMu
  ("cata",
   do f <- newVarType "cata_f"
      a <- newVarType "cata_a"
      return $ functionType (functionType (AppTExpr f a) a) $ functionType (muType f) a,
   const2 $ return $ LambdaGraphValue $ \(LambdaGraphValue cataFun) ->
     return $ LambdaGraphValue $ fix $ \doCata -> \(MuGraphValue (typeName, typeParams, typeBody) innerValue) -> do
       fmapped <- fmapNewtype typeBody (last typeParams) doCata innerValue
       cataFun fmapped
  ),
  -- TODO bayes net!
  ("uniformBool",
   return $ functionType (ConstTExpr "Unit") (ConstTExpr "Bool"),
   const2 $ return $ LambdaGraphValue $ \_ -> do
     v <- newVar boolValueExpFam
     newFactor (expFamFactor boolValueExpFam [] ([0.0], [[]])) [v]
     return $ VarGraphValue v),
  ("standardNormal",
   return $ functionType (ConstTExpr "Unit") (ConstTExpr "Double"),
   const2 $ return $ LambdaGraphValue $ \_ -> do
     v <- newVar gaussianValueExpFam
     newFactor (expFamFactor gaussianValueExpFam [] ([0.0, -0.5], [[]])) [v]
     return $ VarGraphValue v),
  ("true", return (ConstTExpr "Bool"), const2 $ liftM VarGraphValue $ constValue boolValueExpFam $ BoolValue True),
  ("false", return (ConstTExpr "Bool"), const2 $ liftM VarGraphValue $ constValue boolValueExpFam $ BoolValue False),
  -- ("ifthenelse", return $ functionType (ConstTExpr "Bool") $ functionType (ConstTExpr "Bool") (ConstTExpr "Bool"),
  --  const2 $ return $ LambdaGraphValue $ \(VarGraphValue c) ->
  ("randFunction", return (functionType (ConstTExpr "Unit") $ functionType (VarTExpr "a") $ VarTExpr "b"),
   \(AppTExpr (AppTExpr (ConstTExpr "->") (ConstTExpr "Unit")) (AppTExpr (AppTExpr (ConstTExpr "->") argType) resType)) _ ->
     return $ LambdaGraphValue $ \UnitGraphValue -> do
       let argExpFams = typeToExpFams argType
           resExpFams = typeToExpFams resType
       rfs <- mapM (flip newRandFun argExpFams) resExpFams
       return $ LambdaGraphValue $ \argValue -> do
         let argVars = graphValueEmbeddedVars argValue
         resVars <- mapM (flip newSampleFromRandFun argVars) rfs
         return $ varsToGraphValue resType resVars),
  ("boolToDoubleFun", return (functionType (ConstTExpr "Unit") $ functionType (ConstTExpr "Bool") (ConstTExpr "Double")), const2 $ return $ LambdaGraphValue $ \_ -> do
    rf <- newRandFun gaussianValueExpFam [boolValueExpFam]
    return $ LambdaGraphValue $ \(VarGraphValue boolvar) -> liftM VarGraphValue $ newSampleFromRandFun rf [boolvar])
  ]

toHindleyMilnerContext x = (Map.map fst x, Map.empty)

toInterpretContext x = Map.map snd x
