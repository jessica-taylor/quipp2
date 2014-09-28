{-# LANGUAGE RankNTypes, TypeFamilies, NoMonomorphismRestriction #-}

module Quipp.ExpFam (ExpFam(ExpFam, expFamD, expFamSufStat, expFamG, expFamSample),
                     promoteExpFam, expFamMLE,
                     Likelihood(KnownValue, NatParam), promoteLikelihood, negInfinity,
                     timesLikelihood, productLikelihoods, expSufStat,
                     gaussianExpFam, gammaExpFam) where

import Debug.Trace
import Control.Monad (liftM)
import Control.Monad.State.Lazy (State)
import Data.Foldable (foldlM)
import Data.Maybe (fromJust)
import System.Random (RandomGen)
import Numeric.AD (AD, Mode, Scalar, grad, hessian, auto)
import Numeric.Matrix (Matrix)
import qualified Numeric.Matrix as Mat



data ExpFam v = ExpFam {
  expFamD :: Int,
  expFamSufStat :: v -> [Double],
  expFamG :: forall s. (Real s, Floating s, Mode s, Scalar s ~ Double) => [s] -> s,
  expFamSample :: forall g. RandomGen g => State g v
}

promoteExpFam :: (v -> u, u -> v) -> ExpFam v -> ExpFam u
promoteExpFam (f, finv) ef = ExpFam {
  expFamD = expFamD ef,
  expFamSufStat = expFamSufStat ef . finv,
  expFamG = expFamG ef,
  expFamSample = liftM f (expFamSample ef)
}

rowMatrix :: [Double] -> Matrix Double
rowMatrix row = Mat.fromList [row]

colMatrix :: [Double] -> Matrix Double
colMatrix col = Mat.fromList (map return col)

outerProduct :: [Double] -> [Double] -> Matrix Double
outerProduct a b = colMatrix a * rowMatrix b

flatMatrix :: Matrix Double -> [Double]
flatMatrix = concat . Mat.toList

splitListIntoBlocks :: Int -> [a] -> [[a]]
splitListIntoBlocks _ [] = []
splitListIntoBlocks n lst = take n lst : splitListIntoBlocks n (drop n lst)

matrixWithSize :: Int -> Int -> [Double] -> Matrix Double
matrixWithSize rows cols lst
  | rows * cols /= length lst = error "Bad call to matrixWithSize"
  | otherwise = Mat.fromList (splitListIntoBlocks cols lst)

matMulByVector :: Matrix Double -> [Double] -> [Double]
matMulByVector m = flatMatrix . (m*) . colMatrix

dotProduct :: Num a => [a] -> [a] -> a
dotProduct x y = sum (zipWith (+) x y)

adMatMulByVector :: Num a => [a] -> [a] -> [a]
adMatMulByVector mat vec = map (dotProduct vec) (splitListIntoBlocks (length vec) mat)

-- fixZeroRowCols :: Matrix Double -> Matrix Double
-- fixZeroRowCols mat =
--   let isZeroRowCol i = all (== 0.0) (Mat.row i mat ++ Mat.col i mat)
--   in mat + Mat.diag [if isZeroRowCol i then 1.0 else 0.0 | i <- [1 .. Mat.numRows mat]]

newtonMethodStep :: ([Double] -> ([Double], Matrix Double)) -> [Double] -> [Double]
newtonMethodStep f x =
  let (grad, hess) = f x in case Mat.inv (fixZeroRowCols hess) of
    Nothing -> error ("Bad Hessian: " ++ show hess)
    Just invHess -> zipWith (-) x $ matMulByVector invHess grad

newtonMethod :: ([Double] -> ([Double], Matrix Double)) -> [Double] -> [[Double]]
newtonMethod f = iterate (newtonMethodStep f)

expFamMLE :: ExpFam a -> [([Double], [Double])] -> [Double] -> [[Double]]
expFamMLE fam samples etaStart =
  let -- n = length samples
      -- lenFeatures = let (features, _):_ = samples in length features
      -- outerProducts = map (flatMatrix . uncurry (flip outerProduct)) samples
      -- outerProductVariance = map variance (transpose outerProducts)
      -- indepGrad = map sum (transpose outerProducts)
      sampleProb :: (Real m, Floating m, Mode m, Scalar m ~ Double) => [m] -> ([Double], [Double]) -> m
      sampleProb eta (features, ss) = dotProduct np (map auto ss) - expFamG fam np
        where np = adMatMulByVector eta (map auto features)
      f :: (Real m, Floating m, Mode m, Scalar m ~ Double) => [m] -> m
      f eta = sum (map (sampleProb eta) samples)
  in newtonMethod (\eta -> (grad f eta, Mat.fromList $ hessian f eta)) etaStart

data Likelihood v = KnownValue v | NatParam [Double]

promoteLikelihood :: (v -> u, u -> v) -> Likelihood v -> Likelihood u
promoteLikelihood (f, finv) (KnownValue v) = KnownValue (f v)
promoteLikelihood (f, finv) (NatParam np) = NatParam np

timesLikelihood :: Eq v => Likelihood v -> Likelihood v -> Maybe (Likelihood v)
timesLikelihood (KnownValue v1) (KnownValue v2) =
  if v1 == v2 then Just (KnownValue v1) else Nothing
timesLikelihood (KnownValue v1) (NatParam _) = Just $ KnownValue v1
timesLikelihood (NatParam _) (KnownValue v2) = Just $ KnownValue v2
timesLikelihood (NatParam n1) (NatParam n2) = Just $ NatParam (zipWith (+) n1 n2)

productLikelihoods :: Eq v => [Likelihood v] -> Maybe (Likelihood v)
productLikelihoods (l:ls) = foldlM timesLikelihood l ls

expSufStat :: ExpFam v -> Likelihood v -> [Double]
expSufStat ef (KnownValue v) = expFamSufStat ef v
expSufStat ef (NatParam np) = grad (expFamG ef) np

mkExpFam :: [v -> Double] -> (forall s. (Real s, Floating s, Mode s, Scalar s ~ Double) => [s] -> s) -> ExpFam v
mkExpFam fs g = ExpFam {
  expFamD = length fs,
  expFamSufStat = \v -> map ($ v) fs,
  expFamG = g,
  expFamSample = undefined
}

negInfinity :: Double
negInfinity = read "-Infinity"

gaussianExpFam :: ExpFam Double
gaussianExpFam = mkExpFam [id, (^2)] g
  where g :: (Floating a, Mode a, Real a) => [a] -> a
        g [n1, n2] | n2 >= 0 = 0/0
                   | otherwise = let variance = -1 / (2 * n2)
                                     mean = n1 * variance
                                 in log (2 * pi * variance) / 2 + mean^2/(2 * variance)
        g x = error (show $ map toRational x)

-- function log_gamma(xx)
-- {
--     var x = xx - 1.0;
--     var tmp = x + 5.5; tmp -= (x + 0.5)*Math.log(tmp);
--     var ser=1.000000000190015;
--     for (j=0;j<=5;j++){ x++; ser += cof[j]/x; }
--     return -tmp+Math.log(2.5066282746310005*ser);
-- }

gammaExpFam :: ExpFam Double
gammaExpFam = mkExpFam [id, log] undefined
