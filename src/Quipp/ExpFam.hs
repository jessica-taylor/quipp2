{-# LANGUAGE RankNTypes, TypeFamilies, NoMonomorphismRestriction, ScopedTypeVariables, ViewPatterns #-}

module Quipp.ExpFam (ExpFam(ExpFam, expFamName, expFamD, expFamSufStat, expFamG, expFamSample, expFamDefaultNatParam, expFamRandomNatParam),
                     expFamFeaturesD, expFamSufStatToFeatures, expFamFeaturesToSufStat,
                     expFamSufStatToLikelihood, expFamCrossEntropy,
                     getNatParam,
                     Params, mapParams,
                     promoteExpFam, expFamLogProbability, expFamMLE, expFamMH,
                     Likelihood(KnownValue, NatParam), promoteLikelihood, negInfinity,
                     likelihoodLogProbability,
                     timesLikelihood, productLikelihoods,
                     sampleLikelihood, expSufStat, covarianceSufStat,
                     gaussianExpFam, categoricalExpFam,
                     expFamEntropy) where

import Debug.Trace
import Control.Monad (liftM, zipWithM)
import Data.Foldable (foldlM)
import Data.List (groupBy, sortBy)
import Data.Maybe (fromJust)
import Data.Random (RVarT, RVar, normal, gamma)
import Data.Random.Distribution.Categorical (categorical)
import Data.Random.Distribution.Dirichlet (dirichlet)
import Data.Random.Distribution.Exponential (exponential)
import Numeric.AD (AD, Mode, Scalar, grad, hessian)

import Quipp.Util


data ExpFam v = ExpFam {
  expFamName :: String,
  expFamD :: Int,
  expFamSufStat :: v -> [Double],
  expFamG :: forall s. RealFloat s => [s] -> s,
  expFamSufStatToLikelihood :: [Double] -> Likelihood v,
  expFamSample :: [Double] -> RVar v,
  expFamDefaultNatParam :: [Double],
  expFamRandomNatParam :: RVar [Double],
  expFamFeaturesMask :: [Bool]
}

instance Show (ExpFam v) where
  show = expFamName

expFamFeaturesD :: ExpFam v -> Int
expFamFeaturesD = length . filter id . expFamFeaturesMask

expFamSufStatToFeatures :: ExpFam v -> [a] -> [a]
expFamSufStatToFeatures ef ss
  | length ss /= expFamD ef = error "bad suf stat length"
  | otherwise = [s | (s, m) <- zip ss (expFamFeaturesMask ef), m]

expFamFeaturesToSufStat :: Num a => ExpFam v -> [a] -> [a]
expFamFeaturesToSufStat ef features
  | length features /= expFamFeaturesD ef = error "bad features length"
  | otherwise = getSS (expFamFeaturesMask ef) features
    where getSS [] [] = []
          getSS (True:ms) (f:fs) = f : getSS ms fs
          getSS (False:ms) fs = 0 : getSS ms fs
          getSS _ _ = undefined

promoteExpFam :: (v -> u, u -> v) -> ExpFam v -> ExpFam u
promoteExpFam (f, finv) ef = ExpFam {
  expFamName = expFamName ef,
  expFamD = expFamD ef,
  expFamSufStat = expFamSufStat ef . finv,
  expFamG = expFamG ef,
  expFamSufStatToLikelihood = fmap f . expFamSufStatToLikelihood ef,
  expFamSample = liftM f . expFamSample ef,
  expFamRandomNatParam = expFamRandomNatParam ef,
  expFamDefaultNatParam = expFamDefaultNatParam ef,
  expFamFeaturesMask = expFamFeaturesMask ef
}

lineSearch :: ([Double] -> Double) -> [Double] -> [Double] -> [Double]
lineSearch f x dir =
  let points = [zipWith (+) x (map (/ 2^t) dir) | t <- [0 ..]] in
  case filter (\x' -> f x' >= f x) $ take 100 points of
    x':_ -> x'
    [] -> error ("Found nothing better. f x = " ++ show (f x :: Double)) -- x

newtonMethodStep :: ([Double] -> (Double, [Double], Matrix Double)) -> [Double] -> [Double]
newtonMethodStep f x =
  let (val, grad, hess) = f x in
  -- traceShow (val, grad, hess) $
  lineSearch ((\(v, _, _) -> v) . f) x (map (0-) (linSolve hess grad))

newtonMethod :: ([Double] -> (Double, [Double], Matrix Double)) -> [Double] -> [[Double]]
newtonMethod f = iterate (newtonMethodStep f)

mhNewtonMethodProposalDistr :: ([Double] -> (Double, [Double], Matrix Double)) -> [Double] -> [(Double, Double)]
mhNewtonMethodProposalDistr f xs =
  let (val, grad, hess) = f xs
  in [if h >= 0 then (x, infinity) else (x - g / h, -h) | (x, g, h) <- zip3 xs grad (diagonalEntries hess)]

normalLogProb :: Double -> Double -> Double -> Double
normalLogProb mean prec x
  | prec == infinity = if x == mean then 0.0 else negInfinity
  | otherwise = log prec / 2 - prec * (x - mean)^2 / 2

mhNewtonMethodStep :: ([Double] -> (Double, [Double], Matrix Double)) -> [Double] -> RVar [Double]
mhNewtonMethodStep f xs = do
  let propDistr = mhNewtonMethodProposalDistr f xs
  shrinkFactor <- liftM exp $ exponential 1.0
  proposal <- zipWithM (\x (m, p) -> normal (x + (m - x) / shrinkFactor) (sqrt (1 / p))) xs propDistr
  let propLogProb = sum [normalLogProb m p x | (x, (m, p)) <- zip proposal propDistr]
  let reversePropDistr = mhNewtonMethodProposalDistr f proposal
  let revPropLogProb = sum [normalLogProb m p x | (x, (m, p)) <- zip xs reversePropDistr]
  -- let mhLog = fst3 (f proposal) - fst3 (f xs) + revPropLogProb - propLogProb
  let mhLog = fst3 (f proposal) - fst3 (f xs)
  -- traceShow (fst3 (f proposal), fst3 (f xs), mhLog) $ return ()
  logUnitInterval <- exponential 1.0
  return $ if mhLog >= logUnitInterval then proposal else xs

mhNewtonMethod :: ([Double] -> (Double, [Double], Matrix Double)) -> [Double] -> RVar [[Double]]
mhNewtonMethod f x = iterateRVar (mhNewtonMethodStep f) x

ratNum = (fromRational :: Rational -> Double) . toRational

type Params m = ([m], Matrix m)

mapParams f (xs, ys) = (map f xs, map (map f) ys)

paramsToVector :: Params m -> [m]
paramsToVector (base, weights) = base ++ concat weights

vectorToParams :: ExpFam v -> [m] -> Params m
vectorToParams ef ps =
  let d = expFamD ef
      (basePart, weightsPart) = splitAt d ps
  in (basePart, splitListIntoBlocks (expFamFeaturesD ef) weightsPart)

getNatParam :: RealFloat m => ExpFam v -> Params m -> [m] -> [m]
getNatParam ef (etaBase, etaWeights) argFeatures =
  zipWith (+) etaBase (expFamFeaturesToSufStat ef $ matMulByVector etaWeights argFeatures)

expFamLogProbability :: RealFloat m => ExpFam v -> Params m -> [m] -> [m] -> m
expFamLogProbability fam eta argFeatures ss = dotProduct np ss - expFamG fam np
  where np = getNatParam fam eta argFeatures

groupSamplesByFeatures :: [(Double, [Double], [Double])] -> [(Double, [Double], [Double])]
groupSamplesByFeatures samps =
  let grouped = groupAnywhereBy snd3 samps
  in [(totWeight, snd3 (head g), map sum $ transpose [scaleVec (w / totWeight) s | (w, _, s) <- g])
      | g <- grouped, let totWeight = sum $ map fst3 g]

sampleVariances :: [(Double, [Double], [Double])] -> ([Double], [Double])
sampleVariances xs = (var snd3, var thd3)
  where totWeight = sum (map fst3 xs)
        minVar = 0.00001
        -- normalize handles NaN too
        normalize x = if x >= minVar then x else minVar
        var f = map normalize $ zipWith (-) (map (^2) (ev f id)) (ev f (^2))
        ev f g = foldl1 (zipWith (+)) [scaleVec (fst3 x / totWeight) (map g $ f x) | x <- xs]

sampleVariancesWithVar :: [(Double, [Double], [Double], [Double], [Double])] -> ([Double], [Double])
sampleVariancesWithVar xs = (var $ \(_,a,_,_,_) -> a, var $ \(_,_,_,a,_) -> a)
  where totWeight = sum [w | (w, _, _, _, _) <- xs]
        minVar = 0.00001
        -- normalize handles NaN too
        normalize x = if x >= minVar then x else minVar
        var f = map normalize $ zipWith (-) (map (^2) (ev f id)) (ev f (^2))
        ev f g = foldl1 (zipWith (+)) [scaleVec (w / totWeight) (map g $ f x) | x@(w, _, _, _, _) <- xs]

-- normalize entry for feature a, suf stat b, by stdev(b) / stdev(a)
-- that is, regularization factor is proportional to stdev(a) / stdev(b)
  
  

-- Special case for Gaussian (linear regression).  I have confirmed that
-- this is equivalent.  Note that this does not work for VMP or for
-- samples with weight not equal to 1.
expFamMLE :: ExpFam a -> [(Double, [Double], {- [[Double]], -} [Double])] -> Params Double -> [Params Double]
expFamMLE fam samples etaStart | expFamName fam == "gaussian" =
  let nxs = let (_, x, _) = head samples in length x
      xss :: Matrix Double = [1:x | (_, x, _) <- samples]
      ys :: [Double] = [y | (_, _, [y, _]) <- samples]
      beta :: [Double] = matInv (matMul (transpose xss) xss) `matMulByVector` matMulByVector (transpose xss) ys
      predYs :: [Double] = map (dotProduct beta) xss
      resid :: Double = mean [(y - p)^2 | (y, p) <- zip ys predYs]
      resid' = max 0.0001 resid
  in repeat ([head beta / resid', -1 / (2 * resid')], [map (/ resid') (tail beta)])

expFamMLE fam samples etaStart = -- trace ("\nexpFamMLE " ++ show samples) $
  let samples' = groupSamplesByFeatures samples
      (xvars, yvars) = sampleVariances samples
      f :: RealFloat m => [m] -> m
      f eta = -baseReg (fst params) - featReg (snd params) + sum [fromDouble weight * expFamLogProbability fam params (map fromDouble exs) (map fromDouble ys) | (weight, exs, {- varxs, -} ys) <- samples']
        where params = vectorToParams fam eta
              baseReg ns = squareMagnitude $ zipWith (/) ns (map (fromDouble . sqrt) yvars)
              featReg ns = squareMagnitude $ zipWith (*) (concat ns) [sqrt (fromDouble xv / fromDouble yv) | yv <- expFamSufStatToFeatures fam yvars, xv <- xvars]
  in map (vectorToParams fam) $ newtonMethod (\eta -> (f eta, grad f eta, hessian f eta)) $ paramsToVector etaStart

quadApprox :: RealFloat m => (forall n. RealFloat n => [n] -> n) -> [m] -> (m, [m], Matrix m)
quadApprox f x =
  let value = f x
      grd = grad f x
      hess = hessian f x
  in (value, grd, map (map (2*)) hess)

expectationWithVariances :: RealFloat m => (forall n. RealFloat n => [n] -> n) -> [m] -> [m] -> m
expectationWithVariances f ex varx =
  let fex = f ex
      hess = hessian f ex
  in fex + 0.5 * dotProduct varx (diagEntries hess)
  

-- expFamVarMLE :: ExpFam a -> [(Double, [Double], [Double], [Double], [Double])] -> Params Double -> [Params Double]
-- expFamVarMLE fam samples etaStart = -- trace ("\nexpFamMLE " ++ show samples) $
--   let (_, length -> numxs, _, length -> numys, _) = head samples
--       -- samples' = groupSamplesByFeatures samples
--       (xvars, yvars) = sampleVariancesWithVar samples
--       probData :: RealFloat m => [m] -> [m] -> m
--       probData eta xsys = expFamLogProbability fam (vectorToParams fam eta) xs ys
--         where (xs, ys) = splitAt numxs xsys
--       sampleProb :: RealFloat m => [m] -> (Double, [Double], [Double], [Double], [Double]) -> m
--       sampleProb eta (weight, exs, varxs, eys, varys) =
--         fromDouble weight * expectationWithVariances (probData eta) (map fromDouble $ exs ++ eys) (map fromDouble $ varxs ++ varys)
-- 
--       f :: RealFloat m => [m] -> m
--       f eta = -baseReg (fst params) - featReg (snd params) + sum (map (sampleProb eta) samples)
--         where params = vectorToParams fam eta
--               baseReg ns = squareMagnitude $ zipWith (/) ns (map (fromDouble . sqrt) yvars)
--               featReg ns = squareMagnitude $ zipWith (*) (concat ns) [sqrt (fromDouble xv / fromDouble yv) | yv <- expFamSufStatToFeatures fam yvars, xv <- xvars]
--   in map (vectorToParams fam) $ newtonMethod (\eta -> (f eta, grad f eta, hessian f eta)) $ paramsToVector etaStart

expFamMH :: ExpFam a -> [(Double, [Double], [Double])] -> Params Double -> RVar [Params Double]
expFamMH fam samples etaStart =
  let samples' = groupSamplesByFeatures samples
      f :: RealFloat m => [m] -> m
      f eta = sum [fromDouble weight * expFamLogProbability fam params (map fromDouble exs) (map fromDouble ys) | (weight, exs, {- varxs, -} ys) <- samples']
        where params = vectorToParams fam eta
  in liftM (map (vectorToParams fam)) $ mhNewtonMethod (\eta -> (f eta, grad f eta, hessian f eta)) $ paramsToVector etaStart

data Likelihood v = KnownValue v | NatParam [Double] deriving (Eq, Ord, Show)

instance Functor Likelihood where
  fmap f (KnownValue v) = KnownValue (f v)
  fmap _ (NatParam np) = NatParam np

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
productLikelihoods [] = error "Cannot take the product of no likelihoods"

sampleLikelihood :: ExpFam v -> Likelihood v -> RVar v
sampleLikelihood _ (KnownValue v) = return v
sampleLikelihood ef (NatParam np) = expFamSample ef np

likelihoodLogProbability :: Eq v => ExpFam v -> Likelihood v -> v -> Double
likelihoodLogProbability ef (KnownValue a) b | a == b = 0.0
                                             | otherwise = negInfinity
likelihoodLogProbability ef (NatParam np) a = dotProduct np (expFamSufStat ef a) - expFamG ef np

expSufStat :: ExpFam v -> Likelihood v -> [Double]
expSufStat ef (KnownValue v) = expFamSufStat ef v
expSufStat ef (NatParam np) =
  let g = grad (expFamG ef) np
  in if any isNaN g then error ("Bad g gradient: " ++ show np ++ ", " ++ show g)
  else g

covarianceSufStat :: ExpFam v -> Likelihood v -> [[Double]]
covarianceSufStat ef (KnownValue v) = outerProduct ss ss
  where ss = expFamSufStat ef v
covarianceSufStat ef (NatParam np) =
  hessian (expFamG ef) np

expFamCrossEntropy :: Eq v => ExpFam v -> Likelihood v -> Likelihood v -> Double
-- TODO: reasonable?
expFamCrossEntropy ef (KnownValue p) (KnownValue q) | p == q = 0.0
expFamCrossEntropy ef _ (KnownValue q) = infinity
-- E_P(-log Q(X)) = E_P(g(eta_Q) - eta_Q * phi(X)) = g(eta_Q) - eta_Q * E_P(phi(X))
expFamCrossEntropy ef p (NatParam q) = expFamG ef q - dotProduct q (expSufStat ef p)

expFamEntropy :: Eq v => ExpFam v -> Likelihood v -> Double
expFamEntropy ef l = expFamCrossEntropy ef l l
-- 
-- -- KL(P || Q) = H(P) - E_P(-log Q(X))
-- expFamKLDivergence :: Eq v => ExpFam v -> Likelihood v -> Likelihood v -> Double
-- expFamKLDivergence ef p q = expFamEntropy p - expFamCrossEntropy p q

mkExpFam :: String -> [v -> Double] -> (forall s. RealFloat s => [s] -> s) -> ([Double] -> Likelihood v) -> ([Double] -> RVar v) -> RVar [Double] -> [Double] -> [Bool] -> ExpFam v
mkExpFam name fs g like sample np npd mask = ExpFam {
  expFamName = name,
  expFamD = length fs,
  expFamSufStat = \v -> map ($ v) fs,
  expFamG = g,
  expFamSufStatToLikelihood = like,
  expFamSample = sample,
  expFamRandomNatParam = np,
  expFamDefaultNatParam = npd,
  expFamFeaturesMask = mask
}

gaussianExpFam :: ExpFam Double
gaussianExpFam = mkExpFam "gaussian" [id, (^2)] g like sample randParam [0.0, -0.001] [True, False]
  where g :: RealFloat a => [a] -> a
        g [n1, n2] | n2 >= 0 = 0/0
                   | otherwise = let variance = -1 / (2 * n2)
                                     mean = n1 * variance
                                 in log (2 * pi * variance) / 2 + mean^2/(2 * variance)
        g x = error ("bad gaussian natural parameter: " ++ show (map realToDouble x))
        randParam = do
          n1 <- normal 0.0 1.0
          n2 <- exponential 0.1
          return [n1, -n2]
        like [ex, ex2] =
          let var = ex2 - ex^2 in
          if var > 0 then NatParam [ex / var, 1 / (1 * var)] else KnownValue ex
        sample :: [Double] -> RVar Double
        sample [n1, n2] = let variance = -1 / (2 * n2)
                              mean = n1 * variance
                          in normal mean (sqrt variance)
        sample other = error (show other)

categoricalExpFam :: Int -> ExpFam Int
categoricalExpFam n = mkExpFam ("categorical " ++ show n) (map ss [1 .. n-1]) g like sample randParam (replicate (n-1) 0) (replicate (n-1) True)
  where ss i x = if x == i then 1.0 else 0.0
        g :: RealFloat a => [a] -> a
        g x | length x == n-1 = logSumExp (0:x)
            | otherwise = error ("bad categorical natural parameter: " ++ show (map realToDouble x))
        like probs = undefined --halp
        sample :: [Double] -> RVar Int
        sample ns = categorical $ zip (logProbsToProbs (0:ns)) [0..]
        randParam = do
          (p0:probs) <- dirichlet (replicate n 1)
          return $ map (\p -> log p - log p0) probs


-- function log_gamma(xx)
-- {
--     var x = xx - 1.0;
--     var tmp = x + 5.5; tmp -= (x + 0.5)*Math.log(tmp);
--     var ser=1.000000000190015;
--     for (j=0;j<=5;j++){ x++; ser += cof[j]/x; }
--     return -tmp+Math.log(2.5066282746310005*ser);
-- }

-- gammaExpFam :: ExpFam Double
-- gammaExpFam = mkExpFam [id, log] undefined undefined undefined undefined
