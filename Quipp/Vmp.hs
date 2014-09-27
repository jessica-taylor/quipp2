module Quipp.Vmp (VmpState, initVmpState, stepVmpState) where

import Control.Applicative ((<$>), (<*>))
import Data.Foldable (foldlM)
import Data.List (elemIndex)
import Data.Map (Map, (!))
import qualified Data.Map as Map

import Quipp.ExpFam
import Quipp.Factor

type VmpState v = Map VarId (Likelihood v)

initVmpState :: FactorGraph v -> VmpState v
initVmpState g = fmap (\(ef, _) -> NatParam $ replicate (expFamD ef) 0.0) (factorGraphVars g)

varExpSufStat :: FactorGraph v -> VmpState v -> VarId -> [Double]
varExpSufStat graph state varid =
  expSufStat (fst (factorGraphVars graph ! varid)) (state ! varid)


newVarLikelihood :: FactorGraph v -> VmpState v -> VarId -> Maybe (Likelihood v)
newVarLikelihood graph state varid =
  let (_, fids) = factorGraphVars graph ! varid
      fnp (factor, varids) =
        factorNatParam (elemIndex varid varids) $ map (varExpSufStat graph state) varids
  in productLikelihoods $ map (fnp . (factorGraphVars graph !)) fids


updateVar :: FactorGraph v -> VmpState v -> VarId -> Maybe (VmpState v)
updateVar graph state varid =
  Map.insert varid <$> newVarLikelihood graph state varid <*> state

stepVmpState :: FactorGraph v -> VmpState v -> Maybe (VmpState v)
stepVmpState graph state =
  foldlM (\st varid -> updateVar varid graph st) state (Map.keys $ factorGraphVars graph)

