module Quipp.ParamInference where

import Control.Monad (replicateM, zipWithM_)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Random (RVar, RVarT, normal)

import Quipp.BayesNet
import Quipp.ExpFam
import Quipp.Factor
import Quipp.GraphBuilder
import Quipp.TypeInference
import Quipp.Util
import Quipp.Value
import Quipp.Vmp

randTemplateParams :: FactorGraphTemplate v -> RVar FactorGraphParams
randTemplateParams = fmap Map.fromList . mapM getParam . Map.toList . factorGraphTemplateRandFunctions
  where singleNumber = normal 0.0 1.0
        getParam (rfid, (ef, featureEfs, _)) = do
          base <- replicateM (expFamFeaturesD ef) singleNumber
          weights <- replicateM (expFamFeaturesD ef) $ replicateM (sum $ map expFamFeaturesD featureEfs) singleNumber
          return (rfid, (base, weights))

samplerToSamples :: Int -> GraphBuilder Value GraphValue -> GraphBuilder Value [GraphValue]
samplerToSamples n model = do
  LambdaGraphValue sampler <- model
  replicateM n (sampler UnitGraphValue)

takeSamples :: Int -> GraphBuilder Value GraphValue -> FactorGraphParams -> RVar [FrozenGraphValue]
takeSamples n model params = do
  let (template, samps) = runGraphBuilder (samplerToSamples n model)
  assignment <- sampleBayesNet (instantiateTemplate template params)
  return $ map (freezeGraphValue (assignment !)) samps


conditionedNetwork :: TypeExpr -> GraphBuilder Value GraphValue -> [FrozenGraphValue] -> GraphBuilder Value ()
conditionedNetwork t model condValues = do
  samps <- samplerToSamples (length condValues) model
  let cond value samp = do
        unfrozenValue <- unfreezeGraphValue t value
        unifyGraphValues samp unfrozenValue
  zipWithM_ cond condValues samps

type FST = (FactorGraphState Value, FactorGraphParams)

initFst :: FactorGraphTemplate Value -> FST
initFst templ =
  let params = initTemplateParams templ
  in (initFactorGraphState (instantiateTemplate templ params), params)



stepEM :: FactorGraphTemplate Value -> FST -> RVarT Maybe FST
stepEM templ (state, params) = do
  let factorGraph = instantiateTemplate templ params
  newStates <- iterateM 100 (stepMH factorGraph) state
  let params' = traced "\nparams: " $ updateTemplateParams templ params [(1.0, s) | s <- takeEvery 10 (tail newStates)]
  return (last newStates, params')

-- idea: start with params, take samples, do EM, see how close we got?


data ParamInferenceOptions = ParamInferenceOptions {
  optsNumSamples :: Int,
  optsNumEMSteps :: Int
}

inferParameters :: ParamInferenceOptions -> TypeExpr -> GraphBuilder Value GraphValue -> RVar (FactorGraphParams, [FactorGraphParams])
inferParameters opts t model = do
  let (singleSampleTemplate, _) = runGraphBuilder model
  randParams <- randTemplateParams singleSampleTemplate
  samps <- takeSamples (optsNumSamples opts) model randParams
  let condNet = conditionedNetwork t model samps
  let (condTemplate, _) = runGraphBuilder condNet
  let fstGetter = iterateM (optsNumEMSteps opts) (stepEM condTemplate) (initFst condTemplate)
  fstList <- sampleRVarTWith (\(Just x) -> return x) fstGetter
  return (randParams, map snd fstList)

