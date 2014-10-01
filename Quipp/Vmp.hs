module Quipp.Vmp (VmpState, initVmpState, stepVmpState) where

import Debug.Trace
import Control.Applicative ((<$>), (<*>))
import Data.Foldable (foldlM)
import Data.List (elemIndex)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Maybe (fromJust)

import Quipp.ExpFam
import Quipp.Factor
import Quipp.Util

type VmpState v = Map VarId (Likelihood v)

initVmpState :: FactorGraph v -> VmpState v
initVmpState g = fmap (\(ef, _) -> NatParam $ replicate (expFamD ef) 0.0) (factorGraphVars g)

varExpSufStat :: FactorGraph v -> VmpState v -> VarId -> [Double]
varExpSufStat graph state varid =
  expSufStat (fst (factorGraphVars graph ! varid)) (state ! varid)

traced :: Show a => a -> a
traced a = trace (show a) a

newVarLikelihood :: Eq v => FactorGraph v -> VmpState v -> VarId -> Maybe (Likelihood v)
newVarLikelihood graph state varid =
  let (_, fids) = factorGraphVars graph ! varid
      fnp (factor, varids) =
        factorNatParam factor (fromJust $ elemIndex varid varids) $ map (varExpSufStat graph state) varids
  in productLikelihoods $ map (fnp . (factorGraphFactors graph !)) fids


updateVar :: Eq v => FactorGraph v -> VmpState v -> VarId -> Maybe (VmpState v)
updateVar graph state varid = do
  likelihood <- newVarLikelihood graph state varid
  return $ Map.insert varid likelihood state

stepVmpState :: Eq v => FactorGraph v -> VmpState v -> Maybe (VmpState v)
stepVmpState graph state =
  foldlM (\st varid -> updateVar graph st varid) state (Map.keys $ factorGraphVars graph)

updateVarGibbs :: (Eq v, RandomGen g) => FactorGraph v -> VmpState v -> VarId -> RVarT Maybe v
updateVarGibbs graph state varid g = do
  likelihood <- lift (newVarLikelihood graph state varid)
  sampleLikelihood (fst $ factorGraphVars graph ! varid) $ likelihood g

stepGibbs :: Eq v => FactorGraph v -> VmpState v -> RVarT Maybe (VmpState v)
stepGibbs graph state =
  foldlM (\st varid -> updateVarGibbs graph st varid) state (Map.keys $ factorGraphVars graph)
  
