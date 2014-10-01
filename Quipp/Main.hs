module Quipp.Main where

import Quipp.ExpFam
import Quipp.Factor
import Quipp.Vmp
import Quipp.Util


data Value = DoubleValue Double | CategoricalValue Int deriving (Eq, Ord, Show)

fromDoubleValue (DoubleValue a) = a

doublePromoter = (DoubleValue, fromDoubleValue)

fromCategoricalValue (CategoricalValue a) = a
fromCategoricalValue x = error ("aaa " ++ show x)

categoricalPromoter = (CategoricalValue, fromCategoricalValue)

gaussianExpFam2 = promoteExpFam doublePromoter gaussianExpFam

categoricalExpFam2 = promoteExpFam categoricalPromoter (categoricalExpFam 2)

values = map DoubleValue [0.0, 0.1, 0.2, 0.9, 1.0, 1.2, 1.3]

nClusters = 2

clusterVars = [(i, categoricalExpFam2) | i <- [0 .. length values - 1]]

valueVars = [(i + length values, gaussianExpFam2) | i <- [0 .. length values - 1]]

gaussianFactorVars = [(i, expFamFactor gaussianExpFam2 [categoricalExpFam2] [0.1, 2.0, -1, 0], [i + length values, i]) | i <- [0 .. length values - 1]]

constFactorVars = [(i + length values, constFactor gaussianExpFam2 v, [i + length values]) | (i, v) <- zip [0..] values]


-- main = print $ take 20 $ expFamMLE gaussianExpFam [([1], [2.0, 4.0]), ([1], [3.0, 9.0])] [0, -2]
--

factorGraph = makeFactorGraph (clusterVars ++ valueVars) (gaussianFactorVars ++ constFactorVars)

stateList = iterate (>>= stepVmpState factorGraph) $ Just $ initVmpState factorGraph

main = print $ take 10 stateList
