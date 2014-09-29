module Quipp.Main where

import Quipp.ExpFam
import Quipp.Factor
import Quipp.Vmp


main = print $ take 20 $ expFamMLE gaussianExpFam [([1], [2.0, 4.0]), ([1], [3.0, 9.0])] [0, -2]
