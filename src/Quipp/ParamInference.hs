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
        unfrozenValue <- unfreezeGraphValue t value
        unifyGraphValues samp unfrozenValue
        return latent
  zipWithM cond condValues samps

type FST = (FactorGraphState Value, FactorGraphParams)

initFst :: FactorGraphTemplate Value -> RVar FST
initFst templ = do
  params <- randTemplateParams templ
  return (initFactorGraphState (instantiateTemplate templ params), params)


stepEM :: FactorGraphTemplate Value -> FST -> RVarT Maybe FST
stepEM templ (state, params) = do
  let factorGraph = instantiateTemplate templ params
  newStates <- iterateM 100 (stepMH factorGraph) state
  let params' = updateTemplateParams templ params [(1.0, s) | s <- takeEvery 10 (tail newStates)]
  return (last newStates, params')

-- idea: start with params, take samples, do EM, see how close we got?


data ParamInferenceOptions = ParamInferenceOptions {
  optsNumSamples :: Int,
  optsNumEMSteps :: Int
}

inferParameters :: ParamInferenceOptions -> TypeExpr -> GraphBuilder Value GraphValue -> RVar (FactorGraphParams, [([FrozenGraphValue], FactorGraphParams)])
inferParameters opts t model = do
  let (singleSampleTemplate, _) = runGraphBuilder model
  randParams <- randTemplateParams singleSampleTemplate
  samps <- takeSamples (optsNumSamples opts) model randParams
  trace ("samples: " ++ show samps) $ return ()
  let condNet = conditionedNetwork t model (map snd samps)
  let (condTemplate, latents) = runGraphBuilder condNet
  let fstGetter = sampleRVar (initFst condTemplate) >>= iterateM (optsNumEMSteps opts) (stepEM condTemplate)
  fstList <- sampleRVarTWith (\(Just x) -> return x) fstGetter
  let assnValue assn varid = case assn ! varid of
        KnownValue v -> v
        NatParam np -> error ("Gibbs sampling is fuzzy? " ++ show varid ++ ", " ++ show assn)
  return (randParams, [(map (freezeGraphValue (assnValue assn)) latents, params) | (assn, params) <- tail fstList])

