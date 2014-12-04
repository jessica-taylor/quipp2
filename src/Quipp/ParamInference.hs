module Quipp.ParamInference where

import Debug.Trace
import Control.Monad (replicateM, zipWithM)
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

samplerToSamples :: Int -> GraphBuilder Value GraphValue -> GraphBuilder Value [(GraphValue, GraphValue)]
samplerToSamples n model = do
  LambdaGraphValue sampler <- model
  sampGraphValues <- replicateM n (sampler UnitGraphValue)
  return [(x, y) | PairGraphValue x y <- sampGraphValues]

takeSamples :: Int -> GraphBuilder Value GraphValue -> FactorGraphParams -> RVar [(FrozenGraphValue, FrozenGraphValue)]
takeSamples n model params = do
  let (template, samps) = runGraphBuilder (samplerToSamples n model)
  assignment <- sampleBayesNet (instantiateTemplate template params)
  return [(freezeGraphValue (assignment !) latent, freezeGraphValue (assignment !) obs) | (latent, obs) <- samps]


conditionedNetwork :: TypeExpr -> GraphBuilder Value GraphValue -> [FrozenGraphValue] -> GraphBuilder Value [GraphValue]
conditionedNetwork t model condValues = do
  samps <- samplerToSamples (length condValues) model
  let cond value (latent, samp) = do
        unfrozenValue <- unfreezeGraphValue value
        trace ("unfrozen " ++ show unfrozenValue ++ ", samp " ++ show samp) $ return ()
        unifyGraphValues samp unfrozenValue
        return latent
  zipWithM cond condValues samps

type FST = (FactorGraphState Value, FactorGraphParams)

initFst :: FactorGraphTemplate Value -> RVar FST
initFst templ = do
  params <- randTemplateParams 0.001 templ
  return (initFactorGraphState (instantiateTemplate templ params), params)


stepEM :: FactorGraphTemplate Value -> FST -> RVar FST
stepEM templ (state, params) = do
  let factorGraph = instantiateTemplate templ params
  newStates <- sampleRVarTWith (\(Just x) -> return x) $ iterateM 10 (stepMH factorGraph) state
  -- let params' = updateTemplateParams templ params [(1.0, s) | s <- takeEvery 3 (tail newStates)]
  params' <- updateTemplateParamsMH templ params [(1.0, s) | s <- takeEvery 1 (tail newStates)]
  return (last newStates, params')

-- idea: start with params, take samples, do EM, see how close we got?


data ParamInferenceOptions = ParamInferenceOptions {
  optsNumSamples :: Int
}

inferParametersFromSamples :: TypeExpr -> GraphBuilder Value GraphValue -> [FrozenGraphValue] -> RVar [([FrozenGraphValue], FactorGraphParams)]
inferParametersFromSamples t model samps = do
  let condNet = conditionedNetwork t model samps
  let (condTemplate, latents) = runGraphBuilder condNet
  fstList <- sampleRVar (initFst condTemplate) >>= iterateRVar (stepEM condTemplate)
  let assnValue assn varid = case assn ! varid of
        KnownValue v -> v
        NatParam np -> error ("Gibbs sampling is fuzzy? " ++ show varid ++ ", " ++ show assn)
  return [(map (freezeGraphValue (assnValue assn)) latents, params) | (assn, params) <- tail fstList]

inferParameters :: ParamInferenceOptions -> TypeExpr -> GraphBuilder Value GraphValue -> RVar (FactorGraphParams, [FrozenGraphValue], [FrozenGraphValue], [([FrozenGraphValue], FactorGraphParams)])
inferParameters opts t model = do
  let (singleSampleTemplate, _) = runGraphBuilder model
  traceShow singleSampleTemplate $ return ()
  randParams <- randTemplateParams 10.0 singleSampleTemplate
  samps <- takeSamples (optsNumSamples opts) model randParams
  -- trace ("samples: " ++ show samps) $ return ()
  iterativeResults <- inferParametersFromSamples t model (map snd samps)
  return (randParams, map fst samps, map snd samps, iterativeResults)
  

