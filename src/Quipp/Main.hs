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

example2dClustering = ("2d_clustering.quipp", map (uncurry (FPairGraphValue `on` (FValueGraphValue . DoubleValue))) [
  (1.0, 11.0), (2.2, 14.5), (3.4, 17.8), (4.6, 20.5), (5.3, 22.7),
  (1.1, 18.6), (2.3, 21.7), (3.5, 23.8), (4.3, 25.3), (5.5, 28.0)
  ])


main = do
  let (filename, samples) = example1dClustering
  contents <- readFile $ "examples/" ++ filename
  let resultExpr =
        case parse toplevel "FILE" contents of
          Left err -> error $ show err
          Right result -> result
      typed =
        case typeInfer (toHindleyMilnerContext defaultContext) resultExpr of
          Left err -> error err
          Right result -> result
      builder = interpretExpr (toInterpretContext defaultContext) Map.empty typed
      -- (template, result) = runGraphBuilder builder
  print resultExpr
  print typed
  let (AppTExpr (AppTExpr (ConstTExpr "->") _) t) = fst typed
  iters <- sampleRVar $ inferParametersFromSamples t builder samples
  -- (actualParams, actualLatents, samples, iters) <- sampleRVar $ inferParameters (ParamInferenceOptions {optsNumSamples = 20}) t builder
  -- putStrLn $ "ACTUAL PARAMS: " ++ show actualParams
  -- putStrLn $ "ACTUAL LATENTS: " ++ show actualLatents
  -- putStrLn $ "SAMPLES: " ++ show samples
  forM_ iters $ \(latents, params) -> do
    putStrLn $ "LATENTS: " ++ show latents
    fmap utctDayTime getCurrentTime >>= print
    putStrLn $ "EM PARAMS: " ++ show params
    fmap utctDayTime getCurrentTime >>= print
