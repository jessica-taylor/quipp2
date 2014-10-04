{-# LANGUAGE TupleSections #-}

module Quipp.Factor (
  Factor(Factor, factorExpFams, factorLogValue, factorNatParam),
  promoteFactor, constFactor, gaussianFactor, expFamFactor,
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

gaussianFactor :: Factor Double
gaussianFactor =
  Factor {
    factorExpFams = [gaussianExpFam, gaussianExpFam, gammaExpFam],
    factorLogValue = \[[x, x2], [mu, mu2], [prec, logprec]] ->
      -(x2 + mu2 - 2*x*mu) * prec / 2,
    factorNatParam = NatParam .: fnp
  }
  where
    fnp 0 [_, [mu, mu2], [prec, logprec]] = [2*mu * prec/2, -prec/2]
    fnp 1 [[x, x2], _, [prec, logprec]] = [2*x * prec/2, -prec/2]
    fnp 2 [[x, x2], [mu, mu2], _] = [-(x2 + mu2 - 2 * x * mu)/2, 0]

traced x = trace (show x) x

transpose xs = if maximum (map length xs) == 0 then [] else map head xs : transpose (map tail xs)

expFamFactor :: ExpFam v -> [ExpFam v] -> [Double] -> Factor v
expFamFactor ef featureExpFams eta
  | length eta /= expFamD ef * (1 + sum (map expFamD featureExpFams)) =
      error "Wrong number of expfam parameters"
  | otherwise = 
      Factor {
        factorExpFams = ef:featureExpFams,
        factorLogValue = \(ss:features) -> expFamLogProbability ef eta (concat features) ss,
        factorNatParam = NatParam .: fnp
      }
  where fnp 0 (_:features) = linearMatMulByVector eta (1:concat features)
        fnp n (ss:features) =
          let allFeatures = 1 : concat features
              gradProbNp = grad (\np -> dotProduct np (map auto ss) - expFamG ef np) (linearMatMulByVector eta allFeatures)
              minFeatureIndex = sum $ map expFamD $ take (n-1) featureExpFams
              thisArgDim = expFamD (featureExpFams !! (n-1))
              relevantEta = map (take thisArgDim . drop minFeatureIndex) $ splitListIntoBlocks (length allFeatures) eta
          in matMulByVector (transpose relevantEta) gradProbNp

type VarId = Int
type FactorId = Int

data FactorGraph v = FactorGraph {
  factorGraphVars :: Map VarId (ExpFam v, [FactorId]),
  factorGraphFactors :: Map FactorId (Factor v, [VarId])
}

-- makeFactorGraph :: [(VarId, ExpFam v)] -> [(FactorId, Factor v, [VarId])] -> FactorGraph v
-- makeFactorGraph vars factors = FactorGraph (Map.fromList fgv) (Map.fromList fgf)
--   where fgv = [(varid, (ef, [factorid | (factorid, _, vars) <- factors, elem varid vars])) | (varid, ef) <- vars]
--         fgf = [(factorid, (fac, vars)) | (factorid, fac, vars) <- factors]

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

type FactorGraphParams = Map RandFunId [Double]

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

varExpSufStat :: FactorGraph v -> FactorGraphState v -> VarId -> [Double]
varExpSufStat graph state varid =
  expSufStat (fst (factorGraphVars graph ! varid)) (state ! varid)

newVarLikelihood :: Eq v => FactorGraph v -> FactorGraphState v -> VarId -> Maybe (Likelihood v)
newVarLikelihood graph state varid =
  let (_, fids) = factorGraphVars graph ! varid
      fnp (factor, varids) =
        factorNatParam factor (fromJust $ elemIndex varid varids) $ map (varExpSufStat graph state) varids
  in productLikelihoods $ map (fnp . (factorGraphFactors graph !)) fids

initTemplateParams :: FactorGraphTemplate v -> FactorGraphParams
initTemplateParams = fmap getParam . factorGraphTemplateRandFunctions
  where getParam (ef, featureEfs, _) =
          replicate (expFamD ef * (1 + sum (map expFamD featureEfs))) 0.0

updateTemplateParams :: FactorGraphTemplate v -> FactorGraphParams -> FactorGraphState v -> FactorGraphParams
updateTemplateParams template origParams state = Map.mapWithKey updateParam origParams
  where origGraph = instantiateTemplate template origParams
        updateParam randFunId origParam =
          let (ef, featureEfs, factorIds) = factorGraphTemplateRandFunctions template ! randFunId
              factorValues factorId =
                let (_, varids) = factorGraphTemplateFactors template ! factorId
                    ss:fss = map (varExpSufStat origGraph state) varids
                in (ss, concat fss)
          in expFamMLE ef (map factorValues factorIds) origParam !! 10

