module Quipp.TypeInference where

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Applicative ((<$>), (<*>))
import Control.Monad (liftM, zipWithM, forM)
import Control.Monad.State (get, put)
import Control.Monad.State.Lazy (StateT)
import Control.Monad.Trans (lift)

import Quipp.ExpFam
import Quipp.Factor
import Quipp.GraphBuilder
import Quipp.Value

data TypeExpr = VarTExpr String | ConstTExpr String | AppTExpr TypeExpr TypeExpr deriving (Eq, Ord, Show)

data AdtDefinition = AdtDefinition String [String] [(String, [TypeExpr])] deriving (Eq, Ord, Show)

data PatternExpr = VarPExpr String | ConstrPExpr String [PatternExpr] deriving (Eq, Ord, Show)

-- Expressions annotated by type.
data AnnotatedExprBody = VarAExpr String | LambdaAExpr String TypeExpr AnnotatedExpr | AppAExpr AnnotatedExpr AnnotatedExpr | LetAExpr String AnnotatedExpr AnnotatedExpr | LiteralAExpr Value | AdtAExpr AdtDefinition AnnotatedExpr | CaseAExpr AnnotatedExpr [(PatternExpr, AnnotatedExpr)] deriving (Eq, Ord, Show)

type AnnotatedExpr = (TypeExpr, AnnotatedExprBody)

-- Un-annotated expressions.
data Expr = VarExpr String | LambdaExpr String Expr | AppExpr Expr Expr | LetExpr String Expr Expr | LiteralExpr Value | AdtExpr AdtDefinition Expr | CaseExpr Expr [(PatternExpr, Expr)] deriving (Eq, Ord, Show)

type TypeId = Int

type HindleyMilnerState = (Map String TypeExpr, TypeId)

type TypeCheck = StateT HindleyMilnerState (Either String)

functionType a b = AppTExpr (AppTExpr (ConstTExpr "->") a) b

newTypeId :: TypeCheck String
newTypeId = do
  (m, tid) <- get
  put (m, tid + 1)
  return ("_typeid_" ++ show tid)

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


unifyReduced :: TypeExpr -> TypeExpr -> TypeCheck ()

unifyReduced (VarTExpr v) other = do
  (m, count) <- get
  put (Map.insert v other m, count)

unifyReduced other t@(VarTExpr v) = unifyReduced t other

unifyReduced (ConstTExpr a) (ConstTExpr b) | a == b = return ()

unifyReduced (AppTExpr a b) (AppTExpr c d) = do
  unify a c
  unify b d

unifyReduced _ _ = lift (Left "Unification failed")

unify :: TypeExpr -> TypeExpr -> TypeCheck ()

unify a b = do
  a' <- reduceTypeShallow a
  b' <- reduceTypeShallow b
  unifyReduced a' b'


cloneWithNewVars' :: Map String String -> TypeExpr -> TypeCheck (TypeExpr, Map String String)

cloneWithNewVars' m (VarTExpr v) = case Map.lookup v m of
  Just newvar -> return (VarTExpr newvar, m)
  Nothing -> do
    newvar <- newTypeId
    return (VarTExpr newvar, Map.insert v newvar m)

cloneWithNewVars' m (AppTExpr fun arg) = do
  (funType, m') <- cloneWithNewVars' m fun
  (argType, m'') <- cloneWithNewVars' m' arg
  return (AppTExpr funType argType, m'')

cloneWithNewVars' m other = return (other, m)

cloneWithNewVars :: TypeExpr -> TypeCheck TypeExpr
cloneWithNewVars = liftM fst . cloneWithNewVars' Map.empty


type HindleyMilnerContext = (Map String (TypeCheck TypeExpr), Map String TypeExpr)

splitFunctionType :: TypeExpr -> ([TypeExpr], TypeExpr)
splitFunctionType (AppTExpr (AppTExpr (ConstTExpr "->") a) b) =
  let (args, res) = splitFunctionType b in (a:args, res)
splitFunctionType other = ([], other)


hindleyMilnerPattern :: HindleyMilnerContext -> PatternExpr -> TypeExpr -> TypeCheck [(String, TypeExpr)]

hindleyMilnerPattern _ (VarPExpr var) t = return [(var, t)]

hindleyMilnerPattern ctx@(varctx, typectx) (ConstrPExpr constr fields) t =
  case Map.lookup constr varctx of
    Nothing -> lift (Left $ "Unknown constructor " ++ constr)
    Just getConstrType -> do
      constrType <- getConstrType
      let (argTypes, resType) = splitFunctionType constrType
      unify t resType
      if length argTypes /= length fields
      then error "Wrong number of fields in pattern"
      else do
        substs <- zipWithM (hindleyMilnerPattern ctx) fields argTypes
        return $ concat substs


hindleyMilner :: HindleyMilnerContext -> Expr -> TypeCheck AnnotatedExpr

hindleyMilner (vars, _) (VarExpr v) = case Map.lookup v vars of
  Nothing -> lift (Left $ "Unknown variable " ++ v)
  Just getT -> do
    t <- getT
    return (t, VarAExpr v)

hindleyMilner (varctx, typectx) (LambdaExpr var body) = do
  argType <- liftM VarTExpr newTypeId
  bodyAExpr@(bodyType, _) <- hindleyMilner (Map.insert var (return argType) varctx, typectx) body
  return (functionType argType bodyType, LambdaAExpr var argType bodyAExpr)

hindleyMilner ctx (AppExpr fun arg) = do
  funAExpr@(funType, _) <- hindleyMilner ctx fun
  argAExpr@(argType, _) <- hindleyMilner ctx arg
  resultType <- liftM VarTExpr newTypeId
  unify funType (functionType argType resultType)
  return (resultType, AppAExpr funAExpr argAExpr)

hindleyMilner ctx@(varctx, typectx) (LetExpr var value body) = do
  valueAExpr@(valueType, _) <- hindleyMilner ctx value
  bodyAExpr@(bodyType, _) <- hindleyMilner (Map.insert var (cloneWithNewVars valueType) varctx, typectx) body
  return (bodyType, LetAExpr var valueAExpr bodyAExpr)

hindleyMilner ctx (LiteralExpr lit) =
  let t = case lit of
            DoubleValue _ -> "Double"
            BoolValue _ -> "Bool"
  in return (ConstTExpr t, LiteralAExpr lit)

hindleyMilner (varctx, typectx) (AdtExpr defn@(AdtDefinition typeName params cases) body) =
  let newVars = [(caseName, return $ foldr functionType (foldl AppTExpr (ConstTExpr typeName) $ map VarTExpr params) caseFieldTypes ) | (caseName, caseFieldTypes) <- cases]
      varctx' = foldr (uncurry Map.insert) varctx newVars
  in do
    body@(bodyType, _) <- hindleyMilner (varctx', typectx) body
    return (bodyType, AdtAExpr defn body)

hindleyMilner ctx@(varctx, typectx) (CaseExpr value cases) = do
  valueAExpr@(valueType, _) <- hindleyMilner ctx value
  resultType <- liftM VarTExpr newTypeId
  annCases <- forM cases $ \(pat, body) -> do
    substs <- hindleyMilnerPattern ctx pat valueType
    bodyAExpr@(bodyType, _) <- hindleyMilner (foldr (uncurry Map.insert) varctx [(v, return t) | (v, t) <- substs], typectx) body
    unify resultType bodyType
    return (pat, bodyAExpr)
  return (resultType, CaseAExpr valueAExpr annCases)


-- perhaps the rest should be split up?

data GraphValue = VarGraphValue VarId | LambdaGraphValue (GraphValue -> GraphBuilder Value GraphValue) | AdtGraphValue VarId [[GraphValue]]

fromDoubleValue (DoubleValue a) = a
doublePromoter = (DoubleValue, fromDoubleValue)
gaussianExpFamValue = promoteExpFam doublePromoter gaussianExpFam

boolPromoter = (BoolValue . (== 1), \(BoolValue x) -> if x then 1 else 0)
boolExpFamValue = promoteExpFam boolPromoter (categoricalExpFam 2)

expFamForType :: TypeExpr -> ExpFam Value
expFamForType (ConstTExpr "Double") = gaussianExpFamValue
expFamForType (ConstTExpr "Bool") = boolExpFamValue
expFamForType t = error $ "Can't get exponential family for type " ++ show t

makeCaseFunction :: AdtDefinition -> String -> [TypeExpr] -> GraphBuilder Value GraphValue
makeCaseFunction (AdtDefinition typeName typeParams cases) caseName caseTypes = go [] caseTypes
  where go fields [] = undefined -- AdtGraphValue caseName fields
        go fields (t:ts) = return $ LambdaGraphValue $ \nextField ->
          go (fields ++ [nextField]) ts

interpretPattern :: PatternExpr -> GraphValue -> GraphBuilder Value (Maybe [(String, GraphValue)])
interpretPattern (VarPExpr var) value = return $ Just [(var, value)]
-- interpretPattern (ConstrPExpr constr 

interpretExpr :: Map String (GraphBuilder Value GraphValue) -> AnnotatedExpr -> GraphBuilder Value GraphValue

interpretExpr m (_, VarAExpr var) = case Map.lookup var m of
  Nothing -> error ("cannot find variable " ++ var)
  Just val -> val

interpretExpr m (_, LambdaAExpr param _ body) = return $ LambdaGraphValue $
  \arg -> interpretExpr (Map.insert param (return arg) m) body

interpretExpr m (_, AppAExpr fun arg) = do
  funVal <- interpretExpr m fun
  case funVal of
    LambdaGraphValue f -> interpretExpr m arg >>= f
    _ -> error "Function in application expression is not actually a function"

interpretExpr m (_, LetAExpr var value body) = do
  val <- interpretExpr m value
  interpretExpr (Map.insert var (return val) m) body

interpretExpr m (t, LiteralAExpr value) = do
  var <- newVar (expFamForType t)
  newConstFactor var value
  return $ VarGraphValue var

interpretExpr m (t, AdtAExpr defn@(AdtDefinition typeName typeParams cases) body) =
  let newvars = [(caseName, makeCaseFunction defn caseName caseTypes) | (caseName, caseTypes) <- cases]
  in interpretExpr (foldr (uncurry Map.insert) m newvars) body

-- interpretExpr m (t, CaseAExpr value cases) = 


defaultContext :: Map String (TypeCheck TypeExpr, GraphBuilder Value GraphValue)
defaultContext = Map.fromList $ map (\(a, b, c) -> (a, (b, c))) [
  -- unify :: a -> a -> a
  -- conditions on its arguments being equal, returning one of them
  ("unify",
   do a <- newTypeId
      return $ functionType (VarTExpr a) $ functionType (VarTExpr a) $ VarTExpr a,
   return $ LambdaGraphValue $ \(VarGraphValue v1) ->
     return $ LambdaGraphValue $ \(VarGraphValue v2) ->
       liftM VarGraphValue $ conditionEqual v1 v2),
  ("true", return (ConstTExpr "Bool"), liftM VarGraphValue $ constValue boolExpFamValue $ BoolValue True),
  ("false", return (ConstTExpr "Bool"), liftM VarGraphValue $ constValue boolExpFamValue $ BoolValue False),
  ("boolToDoubleFun", return (functionType (ConstTExpr "Bool") $ functionType (ConstTExpr "Bool") (ConstTExpr "Double")), return $ LambdaGraphValue $ \_ -> do
    rf <- newRandFun gaussianExpFamValue [boolExpFamValue]
    return $ LambdaGraphValue $ \(VarGraphValue boolvar) -> liftM VarGraphValue $ newSampleFromRandFun rf [boolvar])
  ]

