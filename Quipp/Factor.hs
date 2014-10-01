module Quipp.Factor (
  Factor(Factor, factorExpFams, factorLogValue, factorNatParam),
  promoteFactor, constFactor, gaussianFactor, expFamFactor,
  VarId, FactorId, FactorGraph(FactorGraph, factorGraphVars, factorGraphFactors),
  makeFactorGraph) where

import Debug.Trace
import Data.Map (Map)
import qualified Data.Map as Map
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

makeFactorGraph :: [(VarId, ExpFam v)] -> [(FactorId, Factor v, [VarId])] -> FactorGraph v
makeFactorGraph vars factors = FactorGraph (Map.fromList fgv) (Map.fromList fgf)
  where fgv = [(varid, (ef, [factorid | (factorid, _, vars) <- factors, elem varid vars])) | (varid, ef) <- vars]
        fgf = [(factorid, (fac, vars)) | (factorid, fac, vars) <- factors]
