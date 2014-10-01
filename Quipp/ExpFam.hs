{-# LANGUAGE RankNTypes, TypeFamilies, NoMonomorphismRestriction #-}

module Quipp.ExpFam (ExpFam(ExpFam, expFamD, expFamSufStat, expFamG, expFamSample),
                     promoteExpFam, expFamLogProbability, expFamMLE,
                     Likelihood(KnownValue, NatParam), promoteLikelihood, negInfinity,
                     timesLikelihood, productLikelihoods,
                     sampleLikelihood, expSufStat,
                     gaussianExpFam, categoricalExpFam, gammaExpFam) where

import Debug.Trace
import Control.Monad (liftM)
import Data.Foldable (foldlM)
import Data.Maybe (fromJust)
import Data.Random (RVarT, RVar, normalT)
import Data.Random.Distribution.Categorical (categoricalT)
import Numeric.AD (AD, Mode, Scalar, grad, hessian, auto)

import Quipp.Util


data ExpFam v = ExpFam {
  expFamD :: Int,
  expFamSufStat :: v -> [Double],
  expFamG :: forall s. (RealFloat s, Mode s, Scalar s ~ Double) => [s] -> s,
  expFamSample :: [Double] -> RVarT m v
}

promoteExpFam :: (v -> u, u -> v) -> ExpFam v -> ExpFam u
promoteExpFam (f, finv) ef = ExpFam {
  expFamD = expFamD ef,
  expFamSufStat = expFamSufStat ef . finv,
  expFamG = expFamG ef,
  expFamSample = liftM f (expFamSample ef)
}

lineSearch :: ([Double] -> Double) -> [Double] -> [Double] -> [Double]
lineSearch f x dir =
  let points = [zipWith (+) x (map (/ 2^t) dir) | t <- [0 ..]] in
  case filter (\x' -> f x' >= f x) $ take 100 points of
    x':_ -> x'
    [] -> x

newtonMethodStep :: ([Double] -> (Double, [Double], Matrix Double)) -> [Double] -> [Double]
newtonMethodStep f x =
  let (val, grad, hess) = f x in
  -- traceShow (val, grad, hess) $
  lineSearch ((\(v, _, _) -> v) . f) x (map (0-) (linSolve hess grad))

newtonMethod :: ([Double] -> (Double, [Double], Matrix Double)) -> [Double] -> [[Double]]
newtonMethod f = iterate (newtonMethodStep f)

traced label fn a = trace (const "" $ "\n" ++ label ++ ": " ++ show (fn a) ++ "\n") a

ratNum = (fromRational :: Rational -> Double) . toRational

expFamLogProbability :: (RealFloat m, Mode m, Scalar m ~ Double) => ExpFam v -> [m] -> [Double] -> [Double] -> m
expFamLogProbability fam eta features ss = dotProduct np (map auto ss) - expFamG fam np
  where np = linearMatMulByVector eta (map auto features)

expFamMLE :: ExpFam a -> [([Double], [Double])] -> [Double] -> [[Double]]
expFamMLE fam samples etaStart =
  let f :: (RealFloat m, Mode m, Scalar m ~ Double) => [m] -> m
      f eta = sum (map (uncurry $ expFamLogProbability fam eta) samples)
  in newtonMethod (\eta -> (f eta, grad f eta, hessian f eta)) etaStart

data Likelihood v = KnownValue v | NatParam [Double] deriving (Eq, Ord, Show)

promoteLikelihood :: (v -> u, u -> v) -> Likelihood v -> Likelihood u
promoteLikelihood (f, finv) (KnownValue v) = KnownValue (f v)
promoteLikelihood (f, finv) (NatParam np) = NatParam np

timesLikelihood :: Eq v => Likelihood v -> Likelihood v -> Maybe (Likelihood v)
timesLikelihood (KnownValue v1) (KnownValue v2) =
  if v1 == v2 then Just (KnownValue v1) else Nothing
timesLikelihood (KnownValue v1) (NatParam _) = Just $ KnownValue v1
timesLikelihood (NatParam _) (KnownValue v2) = Just $ KnownValue v2
timesLikelihood (NatParam n1) (NatParam n2) 
  | length n1 == length n2 = Just $ NatParam (zipWith (+) n1 n2)
  | otherwise = error "Multiplying differently-sized likelihoods"

productLikelihoods :: Eq v => [Likelihood v] -> Maybe (Likelihood v)
productLikelihoods (l:ls) = foldlM timesLikelihood l ls

sampleLikelihood :: ExpFam v -> Likelihood v -> RVarT m v
sampleLikelihood _ (KnownValue v) = return v
sampleLikelihood ef (NatParam np) = expFamSample ef np

expSufStat :: ExpFam v -> Likelihood v -> [Double]
expSufStat ef (KnownValue v) = expFamSufStat ef v
expSufStat ef (NatParam np) = grad (expFamG ef) np

mkExpFam :: [v -> Double] -> (forall s. (RealFloat s, Mode s, Scalar s ~ Double) => [s] -> s) -> (forall g m. (RandomGen g, MonadState m g) => [Double] -> m v) -> ExpFam v
mkExpFam fs g sample = ExpFam {
  expFamD = length fs,
  expFamSufStat = \v -> map ($ v) fs,
  expFamG = g,
  expFamSample = sample
}


gaussianExpFam :: ExpFam Double
gaussianExpFam = mkExpFam [id, (^2)] g sample
  where g :: (RealFloat a, Mode a) => [a] -> a
        g [n1, n2] | n2 >= 0 = 0/0
                   | otherwise = let variance = -1 / (2 * n2)
                                     mean = n1 * variance
                                 in log (2 * pi * variance) / 2 + mean^2/(2 * variance)
        g x = error ("bad gaussian natural parameter: " ++ show (map realToDouble x))
        sample :: [Double] -> RVarT m Double
        sample [n1, n2] = let variance = -1 / (2 * n2)
                              mean = n1 * variance

                          in normalT mean (sqrt variance)

categoricalExpFam :: Int -> ExpFam Int
categoricalExpFam n = mkExpFam (map ss [1 .. n-1]) g
  where ss i x = if x == i then 1.0 else 0.0
        g :: RealFloat a => [a] -> a
        g x | length x == n-1 = logSumExp (0:x)
            | otherwise = error ("bad categorical natural parameter: " ++ show (map realToDouble x))
        sample :: [Double] -> RVarT m Int
        sample ns = categoricalT $ zip (logProbsToProbs (0:ns)) [0..]

-- function log_gamma(xx)
-- {
--     var x = xx - 1.0;
--     var tmp = x + 5.5; tmp -= (x + 0.5)*Math.log(tmp);
--     var ser=1.000000000190015;
--     for (j=0;j<=5;j++){ x++; ser += cof[j]/x; }
--     return -tmp+Math.log(2.5066282746310005*ser);
-- }

gammaExpFam :: ExpFam Double
gammaExpFam = mkExpFam [id, log] undefined undefined
