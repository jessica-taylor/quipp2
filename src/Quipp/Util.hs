{-# LANGUAGE RankNTypes, FlexibleContexts, TypeFamilies #-}
module Quipp.Util where

import Control.Monad (liftM)
import Control.Monad.State.Lazy (runState)
import Debug.Trace
import Data.Function (on)
import Data.List (groupBy, sortBy)
import Data.Random (RandomSource, RVarT, RVar, StdRandom(StdRandom), runRVar, runRVarT, runRVarTWith, stdUniform)
import qualified Data.Packed.Matrix as Mat
import Numeric.LinearAlgebra.Algorithms (linearSolve, pinv)
import Numeric.AD (diff, Mode, Scalar)
import System.Random (StdGen, mkStdGen)

fst3 (a, _, _) = a
snd3 (_, b, _) = b
thd3 (_, _, c) = c

infixr 9 .:
(f .: g) x y = f (g x y)

traced label x = trace (label ++ " " ++ show x) x

takeEvery :: Int -> [a] -> [a]
takeEvery _ [] = []
takeEvery n (x:xs) = x : takeEvery n (drop (n-1) xs)

sampleRVar v = runRVar v StdRandom
sampleRVarT v = runRVarT v StdRandom

sampleRVarTWith :: RandomSource m StdRandom => (forall t. n t -> m t) -> RVarT n a -> m a
sampleRVarTWith f v = runRVarTWith f v StdRandom

infinity :: Double
infinity = read "Infinity"

negInfinity :: Double
negInfinity = read "-Infinity"

funPow :: Int -> (a -> a) -> a -> a
funPow n f x = iterate f x !! n

iterateM :: Monad m => Int -> (a -> m a) -> a -> m [a]
iterateM 0 _ x = return [x]
iterateM n f x = liftM (x:) (f x >>= iterateM (n-1) f)

stateInfList :: (s -> (a, s)) -> s -> [a]
stateInfList f s =
  let (a, s') = f s in a : stateInfList f s'

iterateRVar :: (a -> RVar a) -> a -> RVar [a]
iterateRVar f x = do
  seed <- stdUniform
  return $ stateInfList (\(y, gen) -> let (y', gen') = runState (sampleRVar (f y)) gen in (y', (y', gen'))) (x, mkStdGen seed)

groupAnywhereBy :: Ord b => (a -> b) -> [a] -> [[a]]
groupAnywhereBy f = groupBy ((==) `on` f) . sortBy (compare `on` f)

logSumExp :: RealFloat a => [a] -> a
logSumExp lps = mx + log (sum [exp (lp - mx) | lp <- lps])
  where mx = maximum lps

-- logSumExp :: RealFloat a => [a] -> a
-- logSumExp lps = log $ sum $ map exp lps

logProbsToProbs :: [Double] -> [Double]
logProbsToProbs lps = [exp (lp - lse) | lp <- lps]
  where lse = logSumExp lps

realToDouble :: Real s => s -> Double
realToDouble = fromRational . toRational

type Matrix a = [[a]]

diagonalEntries :: Matrix a -> [a]
diagonalEntries ((x:xs):rows) = x : diagonalEntries (map tail rows)

outerProduct :: Num a => [a] -> [a] -> Matrix a
outerProduct as bs = [[a*b | b <- bs] | a <- as]

splitListIntoBlocks :: Int -> [a] -> [[a]]
splitListIntoBlocks n lst
  | blocksize * n /= length lst = undefined
  | blocksize == 0 = replicate n []
  | otherwise = go blocksize lst
  where blocksize = length lst `div` n
        go _ [] = []
        go k lst = take k lst : go k (drop k lst)

scaleVec :: Num a => a -> [a] -> [a]
scaleVec x = map (x *)

transpose xs = if maximum (map length xs) == 0 then [] else map head xs : transpose (map tail xs)

dotProduct :: Num a => [a] -> [a] -> a
dotProduct x y = sum (zipWith (*) x y)

matMulByVector :: Num a => Matrix a -> [a] -> [a]
matMulByVector m v = map (dotProduct v) m

linSolve :: Matrix Double -> [Double] -> [Double]
linSolve mat d =
  matMulByVector (Mat.toLists $ pinv $ Mat.fromLists mat) d

fromDouble :: Fractional a => Double -> a
fromDouble = fromRational . toRational

{- f(x) = ax^2 + bx + c
 - f'(x) = 2ax + b
 - f''(x) = 2a
 - a = f''(x) / 2
 - b = f'(x) - 2ax
 - c = f(x) - bx - ax^2
 -}
quadApproximation :: (forall a. (Mode a, RealFloat a) => a -> a) -> Double -> (Double, Double, Double)
quadApproximation f x =
  let deriv = diff f x
      deriv2 = diff (diff f :: (forall a. (Mode a, RealFloat a) => a -> a)) x
      a = deriv2 / 2
      b = deriv - 2 * a * x
      c = f x - b * x - a * x * x
  in (c, b, a)


mean xs = sum xs / fromIntegral (length xs)

variance xs = sum [(x-m)^2 | x <- xs] / fromIntegral (length xs) where m = mean xs

covariance xys = sum [(x - ux) * (y - uy) | (x, y) <- xys] / fromIntegral (length xys)
  where ux = mean (map fst xys)
        uy = mean (map snd xys)
