{-# LANGUAGE TupleSections #-}

module Quipp.TypeInference where

import Debug.Trace
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Applicative ((<$>), (<*>))
import Control.Monad (liftM, zipWithM, forM)
import Control.Monad.State (get, put)
import Control.Monad.State.Lazy (State, runState, StateT, runStateT)
import Control.Monad.Trans (lift)

import Quipp.ExpFam
import Quipp.Factor
import Quipp.GraphBuilder
import Quipp.Value

data TypeExpr = VarTExpr String | ConstTExpr String | AppTExpr TypeExpr TypeExpr deriving (Eq, Ord, Show)

data AdtDefinition = AdtDefinition String [String] [(String, [TypeExpr])] deriving (Eq, Ord, Show)

data PatternExpr = VarPExpr String | ConstrPExpr String [PatternExpr] deriving (Eq, Ord, Show)

-- Expressions annotated by type.
data AnnotatedExprBody = VarAExpr String | LambdaAExpr String TypeExpr AnnotatedExpr | AppAExpr AnnotatedExpr AnnotatedExpr | DefAExpr String AnnotatedExpr AnnotatedExpr | LiteralAExpr Value | AdtAExpr AdtDefinition AnnotatedExpr | CaseAExpr AnnotatedExpr [(PatternExpr, AnnotatedExpr)] deriving (Eq, Ord, Show)

type AnnotatedExpr = (TypeExpr, AnnotatedExprBody)

-- Un-annotated expressions.
data Expr = VarExpr String | WithTypeExpr Expr TypeExpr | LambdaExpr String Expr | AppExpr Expr Expr | DefExpr String Expr Expr | LiteralExpr Value | AdtExpr AdtDefinition Expr | CaseExpr Expr [(PatternExpr, Expr)] deriving (Eq, Ord, Show)

type TypeId = Int

type HindleyMilnerState = (Map String TypeExpr, TypeId)

type TypeCheck = StateT HindleyMilnerState (Either String)

functionType a b = AppTExpr (AppTExpr (ConstTExpr "->") a) b
pairType a b = AppTExpr (AppTExpr (ConstTExpr "Pair") a) b
eitherType a b = AppTExpr (AppTExpr (ConstTExpr "Either") a) b

newTypeId :: String -> TypeCheck String
newTypeId str = do
  (m, tid) <- get
  put (m, tid + 1)
  return ("_" ++ str ++ "_" ++ show tid)

newVarType = liftM VarTExpr . newTypeId

reduceTypeShallow :: TypeExpr -> TypeCheck TypeExpr
reduceTypeShallow t@(VarTExpr v) = do
  (m, _) <- get
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
    LambdaAExpr param typ body ->
      LambdaAExpr param <$> reduceTypeDeep typ <*> reduceTypesInAnnotatedExpr body
    AppAExpr fun arg -> AppAExpr <$> reduceTypesInAnnotatedExpr fun <*> reduceTypesInAnnotatedExpr arg
    DefAExpr var value body -> DefAExpr var <$> reduceTypesInAnnotatedExpr value <*> reduceTypesInAnnotatedExpr body
    AdtAExpr defn body -> AdtAExpr defn <$> reduceTypesInAnnotatedExpr body
    CaseAExpr value cases -> CaseAExpr <$> reduceTypesInAnnotatedExpr value <*> mapM (\(pat, body) -> (pat,) <$> reduceTypesInAnnotatedExpr body) cases
    other -> return other
  return (t', abody')


unifyReduced :: TypeExpr -> TypeExpr -> TypeCheck ()

unifyReduced (VarTExpr v) other = do
  (m, count) <- get
  put (Map.insert v other m, count)

unifyReduced other t@(VarTExpr v) = unifyReduced t other

unifyReduced (ConstTExpr a) (ConstTExpr b) | a == b = return ()

unifyReduced (AppTExpr a b) (AppTExpr c d) = do
  unify a c
  unify b d

unifyReduced a b = lift (Left $ "Unification failed: " ++ show a ++ ", " ++ show b)

unify :: TypeExpr -> TypeExpr -> TypeCheck ()

unify a b = do
  a' <- reduceTypeShallow a
  b' <- reduceTypeShallow b
  unifyReduced a' b'


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


hindleyMilner :: HindleyMilnerContext -> Expr -> TypeCheck AnnotatedExpr

hindleyMilner (vars, _) (VarExpr v) = case Map.lookup v vars of
  Nothing -> lift (Left $ "Unknown variable " ++ v)
  Just getT -> do
    t <- getT
    return (t, VarAExpr v)

hindleyMilner ctx (WithTypeExpr expr typ) = do
  aexpr@(exprType, _) <- hindleyMilner ctx expr
  unify exprType typ
  return aexpr

hindleyMilner (varctx, typectx) (LambdaExpr var body) = do
  argType <- newVarType "lambda_arg"
  bodyAExpr@(bodyType, _) <- hindleyMilner (Map.insert var (return argType) varctx, typectx) body
  return (functionType argType bodyType, LambdaAExpr var argType bodyAExpr)

hindleyMilner ctx (AppExpr fun arg) = do
  funAExpr@(funType, _) <- hindleyMilner ctx fun
  argAExpr@(argType, _) <- hindleyMilner ctx arg
  resultType <- newVarType "app_result"
  unify funType (functionType argType resultType)
  return (resultType, AppAExpr funAExpr argAExpr)

hindleyMilner ctx@(varctx, typectx) (DefExpr var value body) = do
  valueAExpr@(valueType, _) <- hindleyMilner ctx value
  bodyAExpr@(bodyType, _) <- hindleyMilner (Map.insert var (cloneWithNewVars valueType) varctx, typectx) body
  return (bodyType, DefAExpr var valueAExpr bodyAExpr)

hindleyMilner ctx (LiteralExpr lit) =
  let t = case lit of
            DoubleValue _ -> "Double"
            BoolValue _ -> "Bool"
  in return (ConstTExpr t, LiteralAExpr lit)

typeInfer :: HindleyMilnerContext -> Expr -> Either String AnnotatedExpr
typeInfer ctx expr = case runStateT (hindleyMilner ctx expr >>= reduceTypesInAnnotatedExpr) (Map.empty, 0) of
  Left err -> Left err
  Right (ex, state) -> Right ex


-- perhaps the rest should be split up?

data GraphValue = VarGraphValue VarId | LambdaGraphValue (GraphValue -> GraphBuilder Value GraphValue) | UnitGraphValue | PairGraphValue GraphValue GraphValue | EitherGraphValue VarId GraphValue GraphValue | PureLeftGraphValue GraphValue | PureRightGraphValue GraphValue

data FrozenGraphValue = FValueGraphValue Value | FUnitGraphValue | FPairGraphValue FrozenGraphValue FrozenGraphValue | FLeftGraphValue FrozenGraphValue | FRightGraphValue FrozenGraphValue deriving (Eq, Ord)

instance Show GraphValue where
  show (VarGraphValue varid) = "$" ++ show varid
  show (LambdaGraphValue _) = "#lambda"
  show UnitGraphValue = "()"
  show (PairGraphValue a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (EitherGraphValue varid left right) = "if " ++ show varid ++ " then Left " ++ show left ++ " else Right " ++ show right
  show (PureLeftGraphValue left) = "(Left " ++ show left ++ ")"
  show (PureRightGraphValue right) = "(Right " ++ show right ++ ")"

instance Show FrozenGraphValue where
  show (FValueGraphValue v) = show v
  show FUnitGraphValue = "()"
  show (FPairGraphValue a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (FLeftGraphValue a) = "(Left " ++ show a ++ ")"
  show (FRightGraphValue b) = "(Right " ++ show b ++ ")"

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
freezeGraphValue _ other = error "Cannot freeze lambdas"

unfreezeGraphValue :: TypeExpr -> FrozenGraphValue -> GraphBuilder Value GraphValue
unfreezeGraphValue _ FUnitGraphValue = return UnitGraphValue
unfreezeGraphValue t (FValueGraphValue value) = VarGraphValue <$> constValue (expFamForType t) value
unfreezeGraphValue (AppTExpr (AppTExpr (ConstTExpr "Pair") firstType) secondType) (FPairGraphValue a b) =
  PairGraphValue <$> unfreezeGraphValue firstType a <*> unfreezeGraphValue secondType b
unfreezeGraphValue
  (AppTExpr (AppTExpr (ConstTExpr "Either") leftType) rightType)
  (FLeftGraphValue value) =
    EitherGraphValue <$> constValue boolValueExpFam (BoolValue False) <*> unfreezeGraphValue leftType value <*> defaultGraphValue rightType
unfreezeGraphValue
  (AppTExpr (AppTExpr (ConstTExpr "Either") leftType) rightType)
  (FRightGraphValue value) =
    EitherGraphValue <$> constValue boolValueExpFam (BoolValue True) <*> defaultGraphValue leftType <*> unfreezeGraphValue rightType value
unfreezeGraphValue t other = error ("Cannot freeze " ++ show other ++ " : " ++ show t)
  
  
  



defaultGraphValue :: TypeExpr -> GraphBuilder Value GraphValue
defaultGraphValue (AppTExpr (AppTExpr (ConstTExpr "pair") firstType) secondType) =
  PairGraphValue <$> defaultGraphValue firstType <*> defaultGraphValue secondType
defaultGraphValue (AppTExpr (AppTExpr (ConstTExpr "either") leftType) rightType) =
  EitherGraphValue <$> newVar boolValueExpFam <*> defaultGraphValue leftType <*> defaultGraphValue rightType
defaultGraphValue (AppTExpr (AppTExpr (ConstTExpr "->") argType) resType) =
  return $ LambdaGraphValue $ const $ defaultGraphValue argType
defaultGraphValue other = liftM VarGraphValue $ newVar $ expFamForType other

expFamForType :: TypeExpr -> ExpFam Value
expFamForType (ConstTExpr "Double") = gaussianValueExpFam
expFamForType (ConstTExpr "Bool") = boolValueExpFam
expFamForType t = error $ "Can't get exponential family for type " ++ show t

-- interpretPattern :: PatternExpr -> GraphValue -> GraphBuilder Value (Maybe [(String, GraphValue)])
-- interpretPattern (VarPExpr var) value = return $ Just [(var, value)]
-- interpretPattern (ConstrPExpr constr 

interpretExpr :: Map String (TypeExpr -> GraphBuilder Value GraphValue) -> AnnotatedExpr -> GraphBuilder Value GraphValue

interpretExpr m (typ, VarAExpr var) = case Map.lookup var m of
  Nothing -> error ("cannot find variable " ++ var)
  Just val -> val typ

interpretExpr m (_, LambdaAExpr param _ body) = return $ LambdaGraphValue $
  \arg -> interpretExpr (Map.insert param (const $ return arg) m) body

interpretExpr m (_, AppAExpr fun arg) = do
  funVal <- interpretExpr m fun
  case funVal of
    LambdaGraphValue f -> interpretExpr m arg >>= f
    _ -> error "Function in application expression is not actually a function"

interpretExpr m (_, DefAExpr var value body) = do
  val <- interpretExpr m value
  interpretExpr (Map.insert var (const $ return val) m) body

interpretExpr m (t, LiteralAExpr value) = do
  var <- newVar (expFamForType t)
  newConstFactor var value
  return $ VarGraphValue var

-- interpretExpr m (t, AdtAExpr defn@(AdtDefinition typeName typeParams cases) body) =
--   let newvars = [(caseName, makeCaseFunction defn caseName caseTypes) | (caseName, caseTypes) <- cases]
--   in interpretExpr (foldr (uncurry Map.insert) m newvars) body

-- interpretExpr m (t, CaseAExpr value cases) = 

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
  -- TODO: this is wrong!
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

-- ifThenElse pvar (PureLeftGraphValue a) (EitherGraphValue p b c) = 
--   EitherGraphValue (

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

unifyGraphValues :: GraphValue -> GraphValue -> GraphBuilder Value GraphValue
unifyGraphValues (VarGraphValue a) (VarGraphValue b) = liftM VarGraphValue $ conditionEqual a b
unifyGraphValues (PairGraphValue a b) (PairGraphValue c d) =
  PairGraphValue <$> unifyGraphValues a c <*> unifyGraphValues b d
unifyGraphValues (EitherGraphValue a b c) (EitherGraphValue d e f) =
  EitherGraphValue <$> conditionEqual a d <*> unifyGraphValues b e <*> unifyGraphValues c f
unifyGraphValues UnitGraphValue UnitGraphValue = return UnitGraphValue
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

defaultContext :: Map String (TypeCheck TypeExpr, TypeExpr -> GraphBuilder Value GraphValue)
defaultContext = Map.fromList $ map (\(a, b, c) -> (a, (b, c))) [
  -- unify :: a -> a -> a
  -- conditions on its arguments being equal, returning one of them
  ("unify",
   do a <- newVarType "unify_type"
      return $ functionType a $ functionType a a,
   const $ return $ LambdaGraphValue $ \v1 ->
     return $ LambdaGraphValue $ \v2 -> unifyGraphValues v1 v2),
  ("unit", return (ConstTExpr "Unit"), const $ return UnitGraphValue),
  ("fst",
   do a <- newVarType "pair_fst"
      b <- newVarType "pair_snd"
      return $ functionType (pairType a b) a,
   const $ return $ LambdaGraphValue $ \(PairGraphValue first _) -> return first),
  ("snd",
   do a <- newVarType "pair_fst"
      b <- newVarType "pair_snd"
      return $ functionType (pairType a b) b,
   const $ return $ LambdaGraphValue $ \(PairGraphValue _ second) -> return second),
  ("pair",
   do a <- newVarType "pair_fst"
      b <- newVarType "pair_snd"
      return $ functionType a $ functionType b $ pairType a b,
   const $ return $ LambdaGraphValue $ \first -> return $ LambdaGraphValue $
     \second -> return $ PairGraphValue first second),
  ("left",
   do a <- newVarType "either_left"
      b <- newVarType "either_right"
      return $ functionType a $ eitherType a b,
   \(AppTExpr _ (AppTExpr (AppTExpr (ConstTExpr "Either") leftType) rightType)) ->
     return $ LambdaGraphValue $ \value -> EitherGraphValue <$> constValue boolValueExpFam (BoolValue False) <*> return value <*> defaultGraphValue rightType),
  ("right",
   do a <- newVarType "either_left"
      b <- newVarType "either_right"
      return $ functionType b $ eitherType a b,
   \(AppTExpr _ (AppTExpr (AppTExpr (ConstTExpr "Either") leftType) rightType)) ->
     return $ LambdaGraphValue $ \value -> EitherGraphValue <$> constValue boolValueExpFam (BoolValue True) <*> defaultGraphValue leftType <*> return value),
  ("either",
   do a <- newVarType "either_left"
      b <- newVarType "either_right"
      return $ functionType b $ eitherType a b,
   const $ return $ LambdaGraphValue $ \(EitherGraphValue isRightVar leftVal rightVal) ->
     return $ LambdaGraphValue $ \(LambdaGraphValue leftHandler) ->
       return $ LambdaGraphValue $ \(LambdaGraphValue rightHandler) -> do
         leftResult <- leftHandler leftVal
         rightResult <- rightHandler rightVal
         ifThenElse isRightVar leftResult rightResult),
         -- TODO bayes net!
  ("uniformBool",
   return $ functionType (ConstTExpr "Unit") (ConstTExpr "Bool"),
   const $ return $ LambdaGraphValue $ \_ -> do
     v <- newVar boolValueExpFam
     newFactor (expFamFactor boolValueExpFam [] ([0.0], [[]])) [v]
     return $ VarGraphValue v),
  ("standardNormal",
   return $ functionType (ConstTExpr "Unit") (ConstTExpr "Double"),
   const $ return $ LambdaGraphValue $ \_ -> do
     v <- newVar gaussianValueExpFam
     newFactor (expFamFactor gaussianValueExpFam [] ([0.0, -0.5], [[]])) [v]
     return $ VarGraphValue v),
  ("true", return (ConstTExpr "Bool"), const $ liftM VarGraphValue $ constValue boolValueExpFam $ BoolValue True),
  ("false", return (ConstTExpr "Bool"), const $ liftM VarGraphValue $ constValue boolValueExpFam $ BoolValue False),
  ("randFunction", return (functionType (ConstTExpr "Unit") $ functionType (VarTExpr "a") $ VarTExpr "b"),
   \(AppTExpr (AppTExpr (ConstTExpr "->") (ConstTExpr "Unit")) (AppTExpr (AppTExpr (ConstTExpr "->") argType) resType)) ->
     return $ LambdaGraphValue $ \UnitGraphValue -> do
       let argExpFams = typeToExpFams argType
           resExpFams = typeToExpFams resType
       rfs <- mapM (flip newRandFun argExpFams) resExpFams
       return $ LambdaGraphValue $ \argValue -> do
         let argVars = graphValueEmbeddedVars argValue
         resVars <- mapM (flip newSampleFromRandFun argVars) rfs
         return $ varsToGraphValue resType resVars),
  ("boolToDoubleFun", return (functionType (ConstTExpr "Unit") $ functionType (ConstTExpr "Bool") (ConstTExpr "Double")), const $ return $ LambdaGraphValue $ \_ -> do
    rf <- newRandFun gaussianValueExpFam [boolValueExpFam]
    return $ LambdaGraphValue $ \(VarGraphValue boolvar) -> liftM VarGraphValue $ newSampleFromRandFun rf [boolvar])
  ]

toHindleyMilnerContext x = (Map.map fst x, Map.empty)

toInterpretContext x = Map.map snd x
