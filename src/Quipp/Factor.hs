{-# LANGUAGE TupleSections #-}

module Quipp.Factor (
  Factor(Factor, factorExpFams, factorLogValue, factorNatParam),
  promoteFactor, constFactor, expFamFactor,
  VarId, FactorId, FactorGraph(FactorGraph, factorGraphVars, factorGraphFactors),
  FactorGraphTemplate(FactorGraphTemplate, factorGraphTemplateVars, factorGraphTemplateFactors),
  makeFactorGraphTemplate, instantiateTemplate,
  FactorGraphState, initFactorGraphState, varExpSufStat, newVarLikelihood,
  FactorGraphParams, initTemplateParams, updateTemplateParams) where

import Control.Monad (liftM)
import Debug.Trace
import Data.List (elemIndex)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Random (RVar)
import Numeric.AD (grad, auto)

import Quipp.ExpFam
import Quipp.Util

data Factor v = Factor {
  factorExpFams :: [ExpFam v],
  factorLogValue :: [[Double]] -> Double,
  factorNatParam :: Int -> [[Double]] -> Likelihood v
}

promoteFactor :: (v -> u, u -> v) -> Factor v -> Factor u
promoteFactor fs fac = Factor {
  factorExpFams = map (promoteExpFam fs) (factorExpFams fac),
  factorLogValue = factorLogValue fac,
  factorNatParam = \i ss -> promoteLikelihood fs (factorNatParam fac i ss)
}

constFactor :: Eq v => ExpFam v -> v -> Factor v
constFactor ss x = Factor {
  factorExpFams = [ss],
  factorLogValue = \[s] -> if ssv == s then 0 else negInfinity,
  factorNatParam = \0 [_] -> KnownValue x
} where ssv = expFamSufStat ss x

-- gaussianFactor :: Factor Double
-- gaussianFactor =
--   Factor {
--     factorExpFams = [gaussianExpFam, gaussianExpFam, gammaExpFam],
--     factorLogValue = \[[x, x2], [mu, mu2], [prec, logprec]] ->
--       -(x2 + mu2 - 2*x*mu) * prec / 2,
--     factorNatParam = NatParam .: fnp
--   }
--   where
--     fnp 0 [_, [mu, mu2], [prec, logprec]] = [2*mu * prec/2, -prec/2]
--     fnp 1 [[x, x2], _, [prec, logprec]] = [2*x * prec/2, -prec/2]
--     fnp 2 [[x, x2], [mu, mu2], _] = [-(x2 + mu2 - 2 * x * mu)/2, 0]


transpose xs = if maximum (map length xs) == 0 then [] else map head xs : transpose (map tail xs)

expFamFactor :: ExpFam v -> [ExpFam v] -> Params Double -> Factor v
expFamFactor ef argExpFams eta@(etaBase, etaWeights) =
  Factor {
    factorExpFams = ef:argExpFams,
    -- TODO filter
    factorLogValue = \(ss:argss) -> expFamLogProbability ef eta (argSsToFeatures argss) ss,
    factorNatParam = NatParam .: fnp
  }
  where argSsToFeatures = concat . zipWith expFamSufStatToFeatures argExpFams
        fnp 0 (_:argss) = getNatParam ef eta $ argSsToFeatures argss
        fnp n (ss:argss) =
          let gradProbNp = grad (\np -> dotProduct np (map auto ss) - expFamG ef np) $ getNatParam ef eta $ argSsToFeatures argss
              minFeatureIndex = sum $ map expFamFeaturesD $ take (n-1) argExpFams
              thisArgDim = expFamFeaturesD (argExpFams !! (n-1))
              relevantWeights = map (take thisArgDim . drop minFeatureIndex) etaWeights
          in expFamFeaturesToSufStat (argExpFams !! (n-1)) $ matMulByVector (transpose relevantWeights) gradProbNp

type VarId = Int
type FactorId = Int

data FactorGraph v = FactorGraph {
  factorGraphVars :: Map VarId (ExpFam v, [FactorId]),
  factorGraphFactors :: Map FactorId (Factor v, [VarId])
}

type RandFunId = Int

data FactorGraphTemplate v = FactorGraphTemplate {
  factorGraphTemplateVars :: Map VarId (ExpFam v, [FactorId]),
  factorGraphTemplateRandFunctions :: Map RandFunId (ExpFam v, [ExpFam v], [FactorId]),
  factorGraphTemplateFactors :: Map FactorId (Either (Factor v) RandFunId, [VarId])
}

makeFactorGraphTemplate :: [(VarId, ExpFam v)] -> [(RandFunId, ExpFam v, [ExpFam v])] -> [(FactorId, Either (Factor v) RandFunId, [VarId])] -> FactorGraphTemplate v
makeFactorGraphTemplate vars randfuns factors = FactorGraphTemplate (Map.fromList fgv) (Map.fromList fgrf) (Map.fromList fgf)
  where fgv = [(varid, (ef, [factorid | (factorid, _, vars) <- factors, elem varid vars])) | (varid, ef) <- vars]
        fgrf = [(rfid, (ef, featureEfs, [factorid | (factorid, Right rfid', _) <- factors, rfid' == rfid])) | (rfid, ef, featureEfs) <- randfuns]
        fgf = [(factorid, (fac, vars)) | (factorid, fac, vars) <- factors]

type FactorGraphParams = Map RandFunId (Params Double)

instantiateTemplate :: FactorGraphTemplate v -> FactorGraphParams -> FactorGraph v
instantiateTemplate templ params =
  FactorGraph {
    factorGraphVars = factorGraphTemplateVars templ,
    factorGraphFactors = Map.mapWithKey fixFactor (factorGraphTemplateFactors templ)
  }
  where fixFactor _ (Left f, vars) = (f, vars)
        fixFactor factorid (Right randfun, var:vars) =
          (expFamFactor (getExpFam var) (map getExpFam vars) (params ! randfun), var:vars)
        getExpFam var = fst (factorGraphTemplateVars templ ! var)


type FactorGraphState v = Map VarId (Likelihood v)

initFactorGraphState :: FactorGraph v -> FactorGraphState v
initFactorGraphState g = fmap (\(ef, _) -> NatParam $ replicate (expFamD ef) 0.0) (factorGraphVars g)

independentSampleFactorGraphState :: FactorGraph v -> FactorGraphState v -> RVar (FactorGraphState v)
independentSampleFactorGraphState factorGraph = liftM Map.fromList . mapM sampleVar . Map.toList
  where sampleVar (id, likelihood) = do
          value <- sampleLikelihood (fst $ factorGraphVars factorGraph ! id) likelihood
          return (id, KnownValue value)

varExpSufStat :: FactorGraph v -> FactorGraphState v -> VarId -> [Double]
varExpSufStat graph state varid =
  expSufStat (fst (factorGraphVars graph ! varid)) (state ! varid)

varExpFeatures :: FactorGraph v -> FactorGraphState v -> VarId -> [Double]
varExpFeatures graph state varid =
  let ef = fst (factorGraphVars graph ! varid)
  in expFamSufStatToFeatures ef $ varExpSufStat graph state varid

newVarLikelihood :: Eq v => FactorGraph v -> FactorGraphState v -> VarId -> Maybe (Likelihood v)
newVarLikelihood graph state varid =
  let (_, fids) = factorGraphVars graph ! varid
      fnp (factor, varids) =
        factorNatParam factor (fromJust $ elemIndex varid varids) $ map (varExpFeatures graph state) varids
  in productLikelihoods $ map (fnp . (factorGraphFactors graph !)) fids

initTemplateParams :: FactorGraphTemplate v -> FactorGraphParams
initTemplateParams = fmap getParam . factorGraphTemplateRandFunctions
  where getParam (ef, featureEfs, _) =
          (expFamDefaultNatParam ef, replicate (expFamFeaturesD ef) $ replicate (sum $ map expFamFeaturesD featureEfs) 0.0001)

traced s x = trace ("\n" ++ s ++ show x) x

updateTemplateParams :: FactorGraphTemplate v -> FactorGraphParams -> [(Double, FactorGraphState v)] -> FactorGraphParams
updateTemplateParams template origParams states = Map.mapWithKey updateParam origParams
  where origGraph = instantiateTemplate template origParams
        updateParam randFunId origParam =
          let (ef, featureEfs, factorIds) = factorGraphTemplateRandFunctions template ! randFunId
              factorValues factorId weight state =
                let (_, svarid:fvarids) = factorGraphTemplateFactors template ! factorId
                in (weight, concat (map (varExpFeatures origGraph state) fvarids),
                    varExpSufStat origGraph state svarid)
          in expFamMLE ef [factorValues factorId weight state | factorId <- factorIds, (weight, state) <- states] origParam !! 20

