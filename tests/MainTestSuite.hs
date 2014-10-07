{-# LANGUAGE ScopedTypeVariables #-}

module Main where


import Debug.Trace
import Quipp.ExpFam
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

main = defaultMain tests

mean xs = sum xs / fromIntegral (length xs)

variance xs = sum [(x-m)^2 | x <- xs] / fromIntegral (length xs) where m = mean xs

covariance xys = sum [(x - ux) * (y - uy) | (x, y) <- xys] / fromIntegral (length xys)
  where ux = mean (map fst xys)
        uy = mean (map snd xys)

traced x = traceShow x x

assertApproxEqual :: Double -> Double -> Double -> IO ()
assertApproxEqual eps x y = assertBool ("Expected " ++ show x ++ ", got " ++ show y) (abs (x - y) <= eps)

gaussianMleTest ys =
  let ([n1, n2], [[]]) = traced $ expFamMLE gaussianExpFam [([], [y, y^2]) | y <- ys] (expFamDefaultNatParam gaussianExpFam, [[]]) !! 20
      var = -1 / (2 * n2)
      mn = n1 * var
  in assertApproxEqual 0.1 (mean ys) mn >> assertApproxEqual 0.1 (variance ys) var

gaussianMleExamples = [
    [1.0, 2.0],
    [-1.5, -1.6, 9.0, 7.0]
  ]

gaussianMleTestUnit = testCase "non-conditioned gaussian MLE" $ mapM_ gaussianMleTest gaussianMleExamples

gaussianCondMleTest samps =
  let ([n1, n2], [[n3]]) = expFamMLE gaussianExpFam [([x], [y, y^2]) | (x, y) <- samps] (expFamDefaultNatParam gaussianExpFam, [[0.0]]) !! 20
      var = -1 / (2 * n2)
      mn0 = n1 * var
      slope = n3 * var
      eux = mean (map fst samps)
      euy = mean (map snd samps)
      evarx = variance (map fst samps)
      evary = variance (map snd samps)
      ecovar = covariance samps
      er = ecovar / sqrt evarx / sqrt evary
      eresid = (1 - er^2) * evary
      eslope = er * sqrt evary / sqrt evarx
      emn0 = euy - eslope * eux
  in do
    assertApproxEqual 0.01 eresid var
    assertApproxEqual 0.01 eslope slope
    assertApproxEqual 0.01 emn0 mn0

gaussianCondMleExamples = [
    [(1.0, 3.0), (2.0, 5.1), (3.0, 6.9)],
    [(5.6, 5.8), (7.8, 1.2), (5.6, 11.0)]
  ]

gaussianCondMleTestUnit = testCase "conditioned gaussian MLE" $ mapM_ gaussianCondMleTest gaussianCondMleExamples


tests = testGroup "ExpFam" [
    gaussianMleTestUnit,
    gaussianCondMleTestUnit
  ]
