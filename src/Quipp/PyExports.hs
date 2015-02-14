{-# LANGUAGE FroeignFunctionInterface, TemplateHaskell #-}
module PyExports where

import System.IO.Unsafe (unsafePerformIO)
import Text.JSON.Generic (encodeJSON, decodeJSON)

import Quipp.BayesNet
import Quipp.ExpFam
import Quipp.Factor
import Quipp.GraphBuilder
import Quipp.Interpreter
import Quipp.Util
import Quipp.Value
import Quipp.Vmp


decodeTemplate :: String -> FactorGraphTemplate Value

decodeParams :: String -> FactorGraphParams
decodeParams = decodeJSON

encodeParams :: FactorGraphParams -> String
encodeParams = encodeJSON

decodeState :: String -> FactorGraphState Value
decodeState = decodeJSON

encodeState :: FactorGraphState Value -> String
encodeState = encodeJSON

pyRandTemplateParams :: String -> IO String

pySampleBayesNet :: String -> String -> IO String

pyInitEM :: String -> IO [String]

pyStepEM :: String -> String -> String -> IO String

initHaPy
pythonExport 'pyRandTemplateParams
pythonExport 'pySampleBayesNet
pythonExport 'pyInitEM
pythonExport 'pyStepEM


"""
Utilities for calling the Haskell code.

pyRandTemplateParams(templ)
  generate random parameters for a given template

pySampleBayesNet(templ, params)
  given template and parameters, return a sample map of varids to value

pyInitEM(templ)
  generate [state, params]

pyStepEM(templ, state, params)
  return [newState, newParams]
"""



