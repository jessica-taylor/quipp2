module Quipp.Util where

import Debug.Trace
import Data.Random (RVarT, RVar, StdRandom(StdRandom), runRVar)
import qualified Data.Packed.Matrix as Mat
import Numeric.LinearAlgebra.Algorithms (linearSolve, pinv)

infixr 9 .:
(f .: g) x y = f (g x y)

sampleRVar v = runRVar v StdRandom

negInfinity :: Double
negInfinity = read "-Infinity"

logSumExp :: RealFloat a => [a] -> a
logSumExp lps = mx + sum (map (\x -> exp (x - mx)) lps)
  where mx = maximum lps

logProbsToProbs :: [Double] -> [Double]
logProbsToProbs lps = [exp (lp - lse) | lp <- lps]
  where lse = logSumExp lps

realToDouble :: Real s => s -> Double
realToDouble = fromRational . toRational

type Matrix a = [[a]]

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


dotProduct :: Num a => [a] -> [a] -> a
dotProduct x y = sum (zipWith (*) x y)

matMulByVector :: Num a => Matrix a -> [a] -> [a]
matMulByVector m v = map (dotProduct v) m

linSolve :: Matrix Double -> [Double] -> [Double]
linSolve mat d = -- traceShow mat $ concat $ Mat.toLists $ linearSolve (Mat.fromLists mat) (Mat.fromLists (map return d))
  matMulByVector (Mat.toLists $ pinv $ Mat.fromLists mat) d


