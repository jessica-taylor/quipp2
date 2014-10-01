module Quipp.Util where

import Data.Random (RVarT, RVar)
import qualified Data.Packed.Matrix as Mat
import Numeric.LinearAlgebra.Algorithms (linearSolve)

infixr 9 .:
(f .: g) x y = f (g x y)


negInfinity :: Double
negInfinity = read "-Infinity"

logSumExp :: RealFloat a => [a] -> a
logSumExp lps = mx + sum (map (\x -> exp (x - mx)) lps)
  where mx = maximum lps

logProbsToProbs :: [Double] -> Double
logProbsToProbs lps = [exp (lp - lse) | lp <- lps]
  where lse = logSumExp lps

realToDouble :: Real s => s -> Double
realToDouble = fromRational . toRational

type Matrix a = [[a]]

outerProduct :: Num a => [a] -> [a] -> Matrix a
outerProduct as bs = [[a*b | b <- bs] | a <- as]

splitListIntoBlocks :: Int -> [a] -> [[a]]
splitListIntoBlocks _ [] = []
splitListIntoBlocks n lst = take n lst : splitListIntoBlocks n (drop n lst)

dotProduct :: Num a => [a] -> [a] -> a
dotProduct x y = sum (zipWith (*) x y)

matMulByVector :: Num a => Matrix a -> [a] -> [a]
matMulByVector m v = map (dotProduct v) m

linSolve :: Matrix Double -> [Double] -> [Double]
linSolve mat d = concat $ Mat.toLists $ linearSolve (Mat.fromLists mat) (Mat.fromLists (map return d))

linearMatMulByVector :: Num a => [a] -> [a] -> [a]
linearMatMulByVector m v = matMulByVector (splitListIntoBlocks (length v) m) v

