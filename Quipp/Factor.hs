module Quipp.Factor (
  Factor(Factor, factorExpFams, factorLogValue, factorNatParam),
  promoteFactor, constFactor, gaussianFactor,
  VarId, FactorId, FactorGraph(FactorGraph, factorGraphVars, factorGraphFactors)) where

import Data.Map (Map)
import qualified Data.Map as Map

import Quipp.ExpFam

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

(f .: g) x y = f (g x y)

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

type VarId = Int
type FactorId = Int

data FactorGraph v = FactorGraph {
  factorGraphVars :: Map VarId (ExpFam v, [FactorId]),
  factorGraphFactors :: Map FactorId (Factor v, [VarId])
}
