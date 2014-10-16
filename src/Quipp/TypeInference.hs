module Quipp.TypeInference where

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Applicative ((<$>), (<*>))
import Control.Monad (liftM)
import Control.Monad.State (get, put)
import Control.Monad.State.Lazy (StateT)
import Control.Monad.Trans (lift)

import Quipp.ExpFam
import Quipp.Factor
import Quipp.GraphBuilder
import Quipp.Value

data TypeExpr = VarTExpr String | ConstTExpr String | AppTExpr TypeExpr TypeExpr deriving (Eq, Ord, Show)

data AdtDefinition = AdtDefinition String [String] [(String, [TypeExpr])]

data AnnotatedExprBody = VarAExpr String | LambdaAExpr String TypeExpr AnnotatedExpr | AppAExpr AnnotatedExpr AnnotatedExpr | LetAExpr String AnnotatedExpr AnnotatedExpr | LiteralAExpr Value | AdtExpr AdtDefinition Expr deriving (Eq, Ord, Show)

type AnnotatedExpr = (TypeExpr, AnnotatedExprBody)

data Expr = VarExpr String | LambdaExpr String Expr | AppExpr Expr Expr | LetExpr String Expr Expr | LiteralExpr Value | AdtExpr AdtDefinition Expr deriving (Eq, Ord, Show)

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


type hindleyMilnerContext = (Map String (TypeCheck TypeExpr), Map String TypeExpr)

hindleyMilner :: HindleyMilnerContext -> Expr -> TypeCheck AnnotatedExpr

hindleyMilner (vars, _) (VarExpr v) = case Map.lookup v vars of
  Nothing -> lift (Left $ "Unknown variable " ++ v)
  Just t -> return (t, VarAExpr v)

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

hindleyMilner (varctx, typectx) (LetExpr var value body) = do
  valueAExpr@(valueType, _) <- hindleyMilner ctx value
  bodyAExpr@(bodyType, _) <- hindleyMilner (Map.insert var (cloneWithNewVars valueType) varctx, typectx) body
  return (bodyType, LetAExpr var valueAExpr bodyAExpr)

hindleyMilner ctx (LiteralExpr lit) =
  let t = case lit of
            DoubleValue _ -> "Double"
            BoolValue _ -> "Bool"
  in return (ConstTExpr t, LiteralAExpr lit)

hindleyMilner (varctx, typectx) (AdtExpr defn@(AdtDefinition typeName params cases) body) =
  let newVars = [(caseName, foldr functionType (foldl AppTExpr typeName params) caseFieldTypes ) | (caseName, caseFieldTypes) <- cases]
      varctx' = foldr (uncurry Map.insert) varctx newVars
  in do
    body@(bodyType, _) <- hindleyMilner (varctx', typectx) body
    return (bodyType, AdtAExpr defn body)


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

interpretExpr :: Map String (GraphBuilder Value GraphValue) -> AnnotatedExpr -> GraphBuilder Value GraphValue

interpretExpr m (_, VarAExpr var) = case Map.lookup var m of
  Nothing -> error ("cannot find variable " ++ var)
  Just val -> val

interpretExpr m (_, LambdaAExpr param _ body) = return $ LambdaGraphValue $
  \arg -> interpretExpr (Map.insert param arg m) body

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

makeCaseFunction :: String -> [TypeExpr] -> GraphBuilder Value GraphValue
makeCaseFunction caseName caseTypes = go [] caseTypes
  where go fields [] = AdtGraphValue caseName fields
        go 

interpretExpr m (t, AdtAExpr (AdtDefinition typeName typeParams cases) body) =
  let caseFunction caseName caseTypes =
    newvars = [(caseName, caseFunction caseName caseTypes) | (caseName, caseTypes) <- cases]
  interpretExpr (foldr (uncurry Map.insert) m' newvars) body


defaultContext :: Map String (TypeCheck TypeExpr, GraphBuilder Value GraphValue)
defaultContext = Map.fromList [
  -- unify :: a -> a -> a
  -- conditions on its arguments being equal, returning one of them
  ("unify",
   do a <- newTypeId
      return $ functionType (VarTExpr a) $ functionType (VarTExpr a) $ VarTExpr a},
   return $ LambdaGraphValue $ \(VarGraphValue v1) ->
     return $ LambdaGraphValue $ \(VarGraphValue v2) ->
       liftM VarGraphValue $ conditionEqual v1 v2
  ("true", return (ConstTExpr "Bool"), constValue $ BoolValue True),
  ("false", return (ConstTExpr "Bool"), constValue $ BoolValue False),
  ("boolToDoubleFun", return (functionType (ConstTExpr "Bool") $ functionType (ConstTExpr "Bool") (ConstTExpr "Double")), return $ LambdaGraphValue $ \_ -> do
    rf <- newRandFun gaussianExpFamValue [boolExpFamValue]
    return $ LambdaGraphValue $ \boolvar -> newSampleFromRandFun rf [boolvar])
  ]

