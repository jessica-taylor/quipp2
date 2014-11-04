module Quipp.Util where

import Control.Monad (liftM)
import Debug.Trace
import Data.Random (RVarT, RVar, StdRandom(StdRandom), runRVar)
import qualified Data.Packed.Matrix as Mat
import Numeric.LinearAlgebra.Algorithms (linearSolve, pinv)

infixr 9 .:
(f .: g) x y = f (g x y)

traced label x = trace (label ++ " " ++ show x) x


sampleRVar v = runRVar v StdRandom

infinity :: Double
infinity = read "Infinity"

negInfinity :: Double
negInfinity = read "-Infinity"

iterateM :: Monad m => Int -> (a -> m a) -> a -> m [a]
iterateM 0 _ x = return [x]
iterateM n f x = liftM (x:) (f x >>= iterateM (n-1) f)

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
linSolve mat d =
  matMulByVector (Mat.toLists $ pinv $ Mat.fromLists mat) d


