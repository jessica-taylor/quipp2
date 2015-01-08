module Quipp.Main where

import Data.Time.Clock (getCurrentTime, utctDayTime)
import Control.Monad (forM_)
import Debug.Trace
import Control.Monad (liftM)
import Control.Monad.Trans (lift)
import Data.Maybe (fromJust)
import Data.Random (RVar, RVarT, runRVarTWith, StdRandom(StdRandom))
import Text.ParserCombinators.Parsec
import Data.Function (on)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.String.Utils (split)

import Quipp.ExpFam
import Quipp.Factor
import Quipp.Vmp
import Quipp.Util
import Quipp.Value
import Quipp.GraphBuilder
import Quipp.Parser
import Quipp.TypeInference
import Quipp.ParamInference

example1dClustering = ("1d_clustering.quipp", map (FValueGraphValue . DoubleValue) [
  1.0, 1.1, 1.2, 1.4, 6.7, 7.9, 8.9, 5.0
  ])

example2dClustering points = ("2d_clustering.quipp", map (uncurry (FPairGraphValue `on` (FValueGraphValue . DoubleValue))) points)
--  (1.5, 11.0), (2.2, 10.5), (1.4, 9.8), (2.5, 20.5), (5.3, 22.7),
--  (1.1, 18.6), (2.3, 21.7), (3.5, 23.8), (4.3, 25.3), (5.5, 28.0)
--  ])

irisData = do
  strs <- readFile "data/iris.data.txt"
  return [(read a :: Double, read c :: Double) | line <- lines strs, line /= "", let [a, b, c, d, e] = split "," line]

main = do
  -- let (filename, samples) = example2dClustering
  datapoints <- irisData
  let (filename, samples) = example2dClustering datapoints
  -- print datapoints
  prelude <- readFile "Quipp/prelude.quipp"
  contents <- readFile $ "examples/" ++ filename
  let fullSource = prelude ++ contents
  let resultExpr =
        case parse toplevel "FILE" fullSource of
          Left err -> error $ show err
          Right result -> result
      builder = interpretExpr (toInterpretContext defaultContext) Map.empty resultExpr
      -- (template, result) = runGraphBuilder builder
  -- print resultExpr
  -- print typed
  let (AppTExpr (AppTExpr (ConstTExpr "->") _) t) = fst typed
  iters <- sampleRVar $ inferParametersFromSamples t builder samples
  -- (actualParams, actualLatents, samples, iters) <- sampleRVar $ inferParameters (ParamInferenceOptions {optsNumSamples = 20}) t builder
  -- putStrLn $ "ACTUAL PARAMS: " ++ show actualParams
  -- putStrLn $ "ACTUAL LATENTS: " ++ show actualLatents
  -- putStrLn $ "SAMPLES: " ++ show samples
  forM_ (take 10 iters) $ \(latents, params) -> do
    print ([v | FValueGraphValue (BoolValue v) <- latents], Map.toList params)
    -- putStrLn $ "LATENTS: " ++ show latents
    -- fmap utctDayTime getCurrentTime >>= print
    -- putStrLn $ "EM PARAMS: " ++ show params
    -- fmap utctDayTime getCurrentTime >>= print
