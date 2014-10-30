module Quipp.Main where

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


{-
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

gaussianRandFunctions = [(0, gaussianExpFam2, [categoricalExpFam2])]

gaussianFactorVars = [(i, Right 0, [i + length values, i]) | i <- [0 .. length values - 1]]

constFactorVars = [(i + length values, Left (constFactor gaussianExpFam2 v), [i + length values]) | (i, v) <- zip [0..] values]


-- main = print $ take 20 $ expFamMLE gaussianExpFam [([1], [2.0, 4.0]), ([1], [3.0, 9.0])] [0, -2]
--

factorGraphTempl = makeFactorGraphTemplate (clusterVars ++ valueVars) gaussianRandFunctions (gaussianFactorVars ++ constFactorVars)

-}

type FST = (FactorGraphState Value, FactorGraphParams)

initFst :: FactorGraphTemplate Value -> FST
initFst templ =
  let params = initTemplateParams templ
  in (initFactorGraphState (instantiateTemplate templ params), params)

iterateM :: Monad m => Int -> (a -> m a) -> a -> m [a]
iterateM 0 _ x = return [x]
iterateM n f x = liftM (x:) (f x >>= iterateM (n-1) f)

vmpStep :: FactorGraphTemplate Value -> FST -> Maybe FST
vmpStep templ (state, params) = do
  let factorGraph = instantiateTemplate templ params
  state' <- stepVmp factorGraph state
  let params' = updateTemplateParams templ params [(1.0, state')]
  return (state', params')

takeEvery :: Int -> [a] -> [a]
takeEvery _ [] = []
takeEvery n (x:xs) = x : takeEvery n (drop (n-1) xs)


gibbsStep :: FactorGraphTemplate Value -> FST -> RVarT Maybe FST
gibbsStep templ (state, params) = do
  let factorGraph = instantiateTemplate templ params
  newStates <- iterateM 100 (stepMH factorGraph) state
  let params' = traced "\nparams: " $ updateTemplateParams templ params [(1.0, s) | s <- takeEvery 10 (tail newStates)]
  return (last newStates, params')

stateList templ = iterate (fromJust . vmpStep templ) (initFst templ)


stateList2 templ = iterateM 20 (gibbsStep templ) (initFst templ)

main = do
  contents <- readFile "examples/2d_clustering.quipp"
  let resultExpr =
        case parse toplevel "FILE" contents of
          Left err -> error $ show err
          Right result -> result
      typed =
        case typeInfer (toHindleyMilnerContext defaultContext) resultExpr of
          Left err -> error err
          Right result -> result
      builder = interpretExpr (toInterpretContext defaultContext) typed
      (template, result) = runGraphBuilder builder
  print resultExpr
  print typed
  print result
  gibbsStates <- runRVarTWith (\(Just x) -> return x) (stateList2 template) StdRandom
  mapM_ (putStrLn . ("\nSTATE " ++) . show) gibbsStates
  -- x <- runRVarTWith (\(Just x) -> return x) stateList2 StdRandom
  -- mapM_ print $ take 10 x
  -- -- x <- runRVarTWith (\(Just x) -> return x) getStateList2 StdRandom
  -- putStrLn "--------"
  -- mapM_ print $ take 10 stateList
