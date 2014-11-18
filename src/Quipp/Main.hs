module Quipp.Main where

import Control.Monad (forM_)
import Debug.Trace
import Control.Monad (liftM)
import Control.Monad.Trans (lift)
import Data.Maybe (fromJust)
import Data.Random (RVar, RVarT, runRVarTWith, StdRandom(StdRandom))
import Text.ParserCombinators.Parsec
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
main = do
  -- contents <- readFile "examples/1d_clustering.quipp"
  contents <- readFile "examples/1d_clustering.quipp"
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
  (actualParams, actualLatents, samples, iters) <- sampleRVar $ inferParameters (ParamInferenceOptions {optsNumSamples = 100}) t builder
  putStrLn $ "ACTUAL PARAMS: " ++ show actualParams
  putStrLn $ "ACTUAL LATENTS: " ++ show actualLatents
  putStrLn $ "SAMPLES: " ++ show samples
  forM_ iters $ \(latents, params) -> do
    putStrLn $ "LATENTS: " ++ show latents
    putStrLn $ "EM PARAMS: " ++ show params
  -- gibbsStates <- runRVarTWith (\(Just x) -> return x) (stateList2 template) StdRandom
  -- mapM_ (putStrLn . ("\nSTATE " ++) . show) gibbsStates
  -- x <- runRVarTWith (\(Just x) -> return x) stateList2 StdRandom
  -- mapM_ print $ take 10 x
  -- -- x <- runRVarTWith (\(Just x) -> return x) getStateList2 StdRandom
  -- putStrLn "--------"
  -- mapM_ print $ take 10 stateList
