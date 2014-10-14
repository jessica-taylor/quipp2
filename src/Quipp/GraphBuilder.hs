



data GraphBuilderState v = GraphBuilderState {
  gbsVars :: [(VarId, ExpFam v)],
  gbsRandFuns :: [(RandFunId, ExpFam v, [ExpFam v])],
  gbsFactors :: [(FactorId, Either (Factor v) RandFunId, [VarId])],
  gbsNextVarId :: VarId,
  gbsNextRandFunId :: RandFunId,
  gbsNextFactorId :: FactorId
}

type GraphBuilder v = State (GraphBuilderState v)


newVar :: ExpFam v -> GraphBuilder v VarId
newVar ef = do
  s <- get
  let v = gbsNextVarId s
  put s { gbsNextVarId = v + 1, gbsVars = (v, ef) : gbsVars s }
  return v

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
  put s { gbsNextFactorId = f + 1, gbsFactors = (f, fac, args) : gbsFactors s }
  return f

newRandFunFactor :: RandFunId -> [VarId] -> GraphBuilder v FactorId
newRandFunFactor rf args = newGeneralFactor (Right rf) args

newSampleFromRandFun :: RandFunId -> [VarId] -> GraphBuilder v VarId
newSampleFromRandFun rf args = do
  s <- get
  let ef = head [e | (rfid, e, _) <- gbsRandFuns s, rfid == rf]
  v <- newVar ef
  newRandFunFactor rf (v:args)
  return v

newFactor :: Factor v -> [VarId] -> GraphBuilder v FactorId
newFactor f args = newGeneralFactor (Left f) args

newConstFactor :: Eq v => VarId -> v -> GraphBuilder v FactorId
newConstFactor var value = do
  s <- get
  let ef = fromJust $ lookup var $ gbsVars s
  newFactor (constFactor ef value) [var]

{-
f <- newRandFun gaussianExpFam [categoricalExpFam 2]
clusters <- replicateM 10 (newVar (catgeoricalExpFam 2))
xs <- mapM (newSampleFromRandFun f . return) clusters
mapM (uncurry newConstFactor) (zip xs values)

let clusters = replicate 10 (uniformCategorical 2)
let xs = map @clusterToValue clusters
condition (xs == ...)


-}
