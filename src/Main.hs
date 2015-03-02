{-# LANGUAGE FlexibleInstances, NoMonomorphismRestriction, ScopedTypeVariables #-}
module Main where

import Debug.Trace (trace, traceShow)
import Control.Monad (liftM, replicateM)
import Control.Applicative ((<$>), (<*>))
import Data.Map (Map, (!))
import qualified Data.Map as Map
import System.Environment (getArgs)
import qualified Text.JSON as JSON
import Data.Maybe (fromJust)
import Data.Random (RVarT, RVar)

import Quipp.BayesNet
import Quipp.ExpFam
import Quipp.Factor
import Quipp.GraphBuilder
import Quipp.Util
import Quipp.Value
import Quipp.Vmp



zip1_2 :: [a] -> [(b, c)] -> [(a, b, c)]
zip1_2 xs yzs = zipWith (\x (y, z) -> (x, y, z)) xs yzs

decodeExpFam :: JSON.JSValue -> ExpFam Value
decodeExpFam ef = case ef !: "type" of
  "gaussian" -> gaussianValueExpFam
  "bernoulli" -> boolValueExpFam
  "categorical" -> categoricalValueExpFam (ef !: "n")

getResult :: JSON.Result a -> a
getResult (JSON.Ok a) = a
getResult (JSON.Error str) = error $ "Error decoding: " ++ str

decodeJSON :: JSON.JSON a => String -> a
decodeJSON = getResult . JSON.decode

infixl 9 !:
(!:) :: JSON.JSON b => JSON.JSValue -> String -> b
(JSON.JSObject obj) !: key = case Map.lookup key (Map.fromList (JSON.fromJSObject obj)) of
  Nothing -> error ("Key not found: " ++ key ++ " in " ++ show obj)
  Just result -> case JSON.readJSON result of
    JSON.Ok a -> a
    JSON.Error str -> error $ "Error looking up " ++ key ++ " in " ++ show obj ++ ": " ++ str
other !: key = error ("Not object: " ++ show other)

instance JSON.JSON (FactorGraphTemplate Value) where
  readJSON m = return $ makeFactorGraphTemplate
      (map convVar (m !: "vars"))
      (zip1_2 [0..] $ map convRandFun (m !: "randFuns"))
      (zip1_2 [0..] $ map convFactor (m !: "factors"))
    where convVar (i, ef) = (i, decodeExpFam ef)
          convRandFun rf =
            (decodeExpFam (rf !: "resExpFam"),
             map decodeExpFam (rf !: "argExpFams"))
          convFactor fac =
            let facinfo = fac !: "factor" in
            (case facinfo !: "type" of
               "randFun" -> Right (facinfo !: "id")
               "uniformCategorical" ->
                 let n = facinfo !: "n" in
                 Left $ expFamFactor (categoricalValueExpFam n) [] (replicate (n - 1) 0.0, replicate (n-1) [])
               "normal" ->
                 let mean = facinfo !: "mean"
                     stdev = facinfo !: "stdev"
                in Left $ expFamFactor gaussianValueExpFam [] ([mean / stdev^2, -1 / (2 * stdev^2)], [[]])
               "constant" -> Left $ constFactor (decodeExpFam (facinfo !: "expFam")) $ case facinfo !: "expFam" !: "type" of
                 "gaussian" -> DoubleValue (facinfo !: "value")
                 "bernoulli" -> BoolValue (facinfo !: "value")
                 "categorical" -> CategoricalValue (facinfo !: "value")
               other -> error $ "Unknown factor type: " ++ other

             , fac !: "argVarIds")
  showJSON _ = undefined

makeJSObject :: [(String, JSON.JSValue)] -> JSON.JSValue
makeJSObject = JSON.JSObject . JSON.toJSObject

instance JSON.JSON Value where
  readJSON js = case js !: "type" of
    "double" -> return $ DoubleValue (js !: "value")
    "bool" -> return $ BoolValue (js !: "value")
    "categorical" -> return $ CategoricalValue (js !: "value")
  showJSON (DoubleValue d) = makeJSObject [("type", JSON.showJSON "double"), ("value", JSON.showJSON d)]
  showJSON (BoolValue b) = makeJSObject [("type", JSON.showJSON "bool"), ("value", JSON.showJSON b)]
  showJSON (CategoricalValue c) = makeJSObject [("type", JSON.showJSON "categorical"), ("value", JSON.showJSON c)]


instance JSON.JSON (Likelihood Value) where
  readJSON x = case getResult $ JSON.readJSON x of
    Left v -> JSON.Ok $ KnownValue v
    Right np -> JSON.Ok $ NatParam np
  showJSON (KnownValue v) = JSON.showJSON (Left v :: Either Value [Double])
  showJSON (NatParam np) = JSON.showJSON (Right np :: Either Value [Double])


pyRandTemplateParams :: FactorGraphTemplate Value -> IO FactorGraphParams
pyRandTemplateParams templ = sampleRVar $ randTemplateParams 10.0 templ

pySampleBayesNet :: FactorGraphTemplate Value -> FactorGraphParams -> IO (FactorGraphState Value)
pySampleBayesNet templ params =
  sampleRVar $ liftM (fmap KnownValue) $ sampleBayesNet (instantiateTemplate templ params)

type FST = (FactorGraphState Value, FactorGraphParams)

pyInitEM :: FactorGraphTemplate Value -> IO FST
pyInitEM templ = do
  params <- sampleRVar $ randTemplateParams 0.001 templ
  return (initFactorGraphState (instantiateTemplate templ params), params)

estimateVariationalDistrs :: FactorGraph Value -> [FactorGraphState Value] -> FactorGraphState Value
estimateVariationalDistrs graph states = Map.mapWithKey f (factorGraphVars graph)
  where initParam ef = (expFamDefaultNatParam ef, replicate (expFamFeaturesD ef) [])
        f k (ef, _) = NatParam $ fst (expFamMLE ef [(1.0, [], expSufStat ef (state ! k)) | state <- states] (initParam ef) !! 10)

sampleState :: FactorGraph Value -> FactorGraphState Value -> RVar (FactorGraphState Value)
sampleState graph = liftM Map.fromList . mapM sampleVar . Map.toList
  where sampleVar (v, like) = do
          value <- sampleLikelihood (fst (factorGraphVars graph ! v)) like
          return (v, KnownValue value)

stateEntropy :: FactorGraph Value -> FactorGraphState Value -> Double
stateEntropy graph state = traced "entropy" $ sum [expFamEntropy ef (state ! k) | (k, (ef, _)) <- Map.toList (factorGraphVars graph)]

stateLogProb :: FactorGraph Value -> FactorGraphState Value -> RVar Double
stateLogProb graph state = do
  stateSamps <- replicateM 20 (sampleState graph state)
  let stateScore state = sum [factorLogValue fac (map (state !) vars) | (_, (fac, vars)) <- Map.toList (factorGraphFactors graph)]
  return $ traced "logProb" $ mean $ map stateScore stateSamps

-- pyStepEM :: FactorGraphTemplate Value -> FST -> IO (FST, Double)
-- pyStepEM templ (state, params) = sampleRVar $ do
--   let factorGraph = instantiateTemplate templ params
--   newStates <- sampleRVarTWith (\(Just x) -> return x) $ iterateM 20 (stepMH factorGraph) state
--   -- TODO interleaving
--   let q = estimateVariationalDistrs factorGraph newStates
--   let score = stateLogProb factorGraph q + stateEntropy factorGraph q
--   let params' = updateTemplateParams templ params [(1.0, s) | s <- takeEvery 1 (tail newStates)]
--   return ((last newStates, params'), score)

pyScore :: FactorGraphTemplate Value -> FST -> IO Double
pyScore templ (state, params) = do
  let factorGraph = instantiateTemplate templ params
  logProb <- sampleRVar $ stateLogProb factorGraph state
  let score = logProb + stateEntropy factorGraph state
  return score

pyInferState :: FactorGraphTemplate Value -> Int -> FST -> IO (FactorGraphState Value)
pyInferState templ iters (state, params) = do
  let factorGraph = instantiateTemplate templ params
  return $ iterate (fromJust . stepVmp factorGraph) state !! iters

pyInferParams :: FactorGraphTemplate Value -> FST -> IO FactorGraphParams
pyInferParams templ (state, params) = sampleRVar $ do
  let factorGraph = instantiateTemplate templ params
  stateSamps <- replicateM 20 (sampleState factorGraph state)
  return $ updateTemplateParams templ params [(1.0, s) | s <- stateSamps]

pyStepEM' :: FactorGraphTemplate Value -> FST -> IO FST
pyStepEM' templ (state, params) = sampleRVar $ do
  let factorGraph = instantiateTemplate templ params
  let newState = iterate (fromJust . stepVmp factorGraph) state !! 10
  -- TODO interleaving
  -- let score = stateLogProb factorGraph newState + stateEntropy factorGraph newState
  stateSamps <- sampleRVar $ replicateM 20 (sampleState factorGraph newState)
  let params' = updateTemplateParams templ params [(1.0, s) | s <- stateSamps]
  -- return ((last stateSamps, params'), score)
  return (newState, params')


main = do
  [command] <- getArgs
  argsString <- getContents
  let args = decodeJSON argsString
  outputText <- case command of
    "randTemplateParams" -> do
      let [templ] = args
      liftM JSON.encode (pyRandTemplateParams templ)
    "sampleBayesNet" -> do
      let (templ :: FactorGraphTemplate Value, params :: FactorGraphParams) = args
      liftM JSON.encode (pySampleBayesNet templ params)
    "initEM" -> do
      let [templ :: FactorGraphTemplate Value] = args
      liftM JSON.encode (pyInitEM templ)
    "inferState" -> do
      let (templ :: FactorGraphTemplate Value, state :: FactorGraphState Value, params :: FactorGraphParams, iters :: Int) = args
      liftM JSON.encode (pyInferState templ iters (state, params))
    "inferParams" -> do
      let (templ :: FactorGraphTemplate Value, state :: FactorGraphState Value, params :: FactorGraphParams) = args
      liftM JSON.encode (pyInferParams templ (state, params))
    "score" -> do
      let (templ :: FactorGraphTemplate Value, state :: FactorGraphState Value, params :: FactorGraphParams) = args
      liftM JSON.encode (pyScore templ (state, params))
  putStr outputText

