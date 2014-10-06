module Quipp.Main where

import Debug.Trace
import Control.Monad (liftM)
import Control.Monad.Trans (lift)
import Data.Maybe (fromJust)
import Data.Random (RVar, RVarT, runRVarTWith, StdRandom(StdRandom))

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

gaussianRandFunctions = [(0, gaussianExpFam2, [categoricalExpFam2])]

gaussianFactorVars = [(i, Right 0, [i + length values, i]) | i <- [0 .. length values - 1]]

constFactorVars = [(i + length values, Left (constFactor gaussianExpFam2 v), [i + length values]) | (i, v) <- zip [0..] values]


-- main = print $ take 20 $ expFamMLE gaussianExpFam [([1], [2.0, 4.0]), ([1], [3.0, 9.0])] [0, -2]
--

factorGraphTempl = makeFactorGraphTemplate (clusterVars ++ valueVars) gaussianRandFunctions (gaussianFactorVars ++ constFactorVars)

type FST = (FactorGraphState Value, FactorGraphParams)

initFst :: FST
initFst =
  let params = initTemplateParams factorGraphTempl
  in (initFactorGraphState (instantiateTemplate factorGraphTempl params), params)


vmpStep :: FST -> Maybe FST
vmpStep (state, params) = do
  let factorGraph = instantiateTemplate factorGraphTempl params
  state' <- stepVmp factorGraph state
  let params' = updateTemplateParams factorGraphTempl params state'
  return (state', params')

gibbsStep :: FST -> RVarT Maybe FST
gibbsStep (state, params) = do
  let factorGraph = instantiateTemplate factorGraphTempl params
  state' <- stepGibbs factorGraph state
  let params' = updateTemplateParams factorGraphTempl params state'
  return (state', params')

stateList = iterate (fromJust . vmpStep) initFst

iterateM :: Monad m => Int -> (a -> m a) -> a -> m [a]
iterateM 0 _ x = return [x]
iterateM n f x = liftM (x:) (f x >>= iterateM (n-1) f)

stateList2 = iterateM 10 gibbsStep initFst

-- getStateList2 :: RVarT Maybe [VmpState Value]
-- getStateList2 = iterateM 10 (stepGibbs  factorGraph) (initVmpState factorGraph)

main = do
  x <- runRVarTWith (\(Just x) -> return x) stateList2 StdRandom
  mapM_ print $ take 10 x
  -- x <- runRVarTWith (\(Just x) -> return x) getStateList2 StdRandom
  -- print (map snd $ take 20 stateList)