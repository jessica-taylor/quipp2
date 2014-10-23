
module Quipp.GraphBuilder where

import Control.Monad.State (get, put)
import Control.Monad.State.Lazy (State, runState)
import Data.Maybe (fromJust)
import Data.Map (Map)
import qualified Data.Map as Map


import Quipp.ExpFam
import Quipp.Factor



data GraphBuilderState v = GraphBuilderState {
  gbsVars :: [(VarId, ExpFam v)],
  gbsRandFuns :: [(RandFunId, ExpFam v, [ExpFam v])],
  gbsFactors :: [(FactorId, Either (Factor v) RandFunId, [VarId])],
  gbsNextVarId :: VarId,
  gbsNextRandFunId :: RandFunId,
  gbsNextFactorId :: FactorId,
  gbsVarReplacements :: Map VarId VarId
}

type GraphBuilder v = State (GraphBuilderState v)

runGraphBuilder :: GraphBuilder v a -> (FactorGraphTemplate v, a)
runGraphBuilder gb =
  let initState = GraphBuilderState {
          gbsVars = [],
          gbsRandFuns = [],
          gbsFactors = [],
          gbsNextVarId = 0,
          gbsNextRandFunId = 0,
          gbsNextFactorId = 0,
          gbsVarReplacements = Map.empty
        }
      (x, endState) = runState gb initState
      templ = makeFactorGraphTemplate (gbsVars endState) (gbsRandFuns endState) (gbsFactors endState)
  in (templ, x)


newVar :: ExpFam v -> GraphBuilder v VarId
newVar ef = do
  s <- get
  let v = gbsNextVarId s
  put s { gbsNextVarId = v + 1, gbsVars = (v, ef) : gbsVars s }
  return v

resolveVar :: VarId -> GraphBuilder v VarId
resolveVar varid = do
  s <- get
  case Map.lookup varid (gbsVarReplacements s) of
    Just rep -> return rep
    Nothing -> return varid

newRandFun :: ExpFam v -> [ExpFam v] -> GraphBuilder v RandFunId
newRandFun ef argefs = do
  s <- get
  let r = gbsNextRandFunId s
  put s { gbsNextRandFunId = r + 1, gbsRandFuns = (r, ef, argefs) : gbsRandFuns s }
  return r

newGeneralFactor :: Either (Factor v) RandFunId -> [VarId] -> GraphBuilder v FactorId
newGeneralFactor fac args = do
  s <- get
  let f = gbsNextFactorId s
  args' <- mapM resolveVar args
  put s { gbsNextFactorId = f + 1, gbsFactors = (f, fac, args') : gbsFactors s }
  return f

newRandFunFactor :: RandFunId -> [VarId] -> GraphBuilder v FactorId
newRandFunFactor rf args = newGeneralFactor (Right rf) args

newSampleFromRandFun :: RandFunId -> [VarId] -> GraphBuilder v VarId
newSampleFromRandFun rf args = do
  s <- get
  let ef = head [e | (rfid, e, _) <- gbsRandFuns s, rfid == rf]
  v <- newVar ef
  args' <- mapM resolveVar args
  newRandFunFactor rf (v:args')
  return v

newFactor :: Factor v -> [VarId] -> GraphBuilder v FactorId
newFactor f args = newGeneralFactor (Left f) args

getVarExpFam :: VarId -> GraphBuilder v (ExpFam v)
getVarExpFam varid = do
  s <- get
  var' <- resolveVar var
  return $ fromJust $ lookup var' $ gbsVars s

newConstFactor :: Eq v => VarId -> v -> GraphBuilder v FactorId
newConstFactor var value = do
  s <- get
  var' <- resolveVar var
  let ef = fromJust $ lookup var' $ gbsVars s
  newFactor (constFactor ef value) [var']

constValue :: Eq v => ExpFam v -> v -> GraphBuilder v VarId
constValue ef value = do
  v <- newVar ef
  newConstFactor v value
  return v

conditionEqual :: VarId -> VarId -> GraphBuilder v VarId
conditionEqual v1 v2 = do
  s <- get
  let replace varid | varid == v2 = v1
                    | otherwise = varid
  put $ s {
      gbsVars = filter ((/= v2) . fst) (gbsVars s),
      gbsFactors = [(a, b, map replace vars) | (a, b, vars) <- gbsFactors s],
      gbsVarReplacements = Map.insert v2 v1 (gbsVarReplacements s)
    }
  return v1

{-
f <- newRandFun gaussianExpFam [categoricalExpFam 2]
clusters <- replicateM 10 (newVar (catgeoricalExpFam 2))
xs <- mapM (newSampleFromRandFun f . return) clusters
mapM (uncurry newConstFactor) (zip xs values)

let clusters = replicate 10 (uniformCategorical 2)
let xs = map @clusterToValue clusters
condition (xs == ...)


-}
