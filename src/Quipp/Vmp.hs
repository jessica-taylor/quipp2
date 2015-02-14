module Quipp.Vmp where

import Debug.Trace
import Control.Applicative ((<$>), (<*>))
import Control.Monad.Trans.Class (lift)
-- import transformers-0.3.0.0:Control.Monad.Trans.Class (lift)
import Data.Foldable (foldlM)
import Data.List (elemIndex)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Random (RVarT, RVar, normalT)
import Data.Random.Distribution.Exponential (exponentialT)

import Quipp.ExpFam
import Quipp.Factor
import Quipp.Util


updateVarVmp :: Eq v => FactorGraph v -> FactorGraphState v -> VarId -> Maybe (FactorGraphState v)
updateVarVmp graph state varid = do
  likelihood <- newVarLikelihood graph state varid
  return $ Map.insert varid likelihood state

stepVmp :: Eq v => FactorGraph v -> FactorGraphState v -> Maybe (FactorGraphState v)
stepVmp graph state =
  foldlM (\st varid -> updateVarVmp graph st varid) state (Map.keys $ factorGraphVars graph)

updateVarGibbs :: Eq v => FactorGraph v -> FactorGraphState v -> VarId -> RVarT Maybe (FactorGraphState v)
updateVarGibbs graph state varid = do
  likelihood <- lift (newVarLikelihood graph state varid)
  value <- sampleRVar $ sampleLikelihood (fst $ factorGraphVars graph ! varid) $ likelihood
  return $ Map.insert varid (KnownValue value) state

stepGibbs :: Eq v => FactorGraph v -> FactorGraphState v -> RVarT Maybe (FactorGraphState v)
stepGibbs graph state =
  foldlM (\st varid -> updateVarGibbs graph st varid) state (Map.keys $ factorGraphVars graph)

updateVarMH :: Eq v => FactorGraph v -> FactorGraphState v -> VarId -> RVarT Maybe (FactorGraphState v)
updateVarMH graph state varid = do
  let (ef, factorids) = factorGraphVars graph ! varid
  likelihood <- lift (newVarLikelihood graph state varid)
  proposal <- sampleRVar $ sampleLikelihood ef $ likelihood
  let proposalState = Map.insert varid (KnownValue proposal) state
  case state ! varid of
    NatParam _ -> return proposalState
    KnownValue oldValue -> do
      proposalStateLikelihood <- lift (newVarLikelihood graph proposalState varid)
      let stateLp s = sum (map (factorExpLogValue graph s) factorids)
          mhLog = stateLp proposalState - likelihoodLogProbability ef likelihood proposal
                  - stateLp state + likelihoodLogProbability ef proposalStateLikelihood oldValue
      if mhLog >= 0 then return proposalState
      else do
        logUnitInterval <- exponentialT 1.0
        return $ if mhLog >= logUnitInterval then proposalState else state

stepMH :: Eq v => FactorGraph v -> FactorGraphState v -> RVarT Maybe (FactorGraphState v)
stepMH graph state =
  foldlM (\st varid -> updateVarMH graph st varid) state (Map.keys $ factorGraphVars graph)
