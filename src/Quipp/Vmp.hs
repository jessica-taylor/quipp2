module Quipp.Vmp where

import Debug.Trace
import Control.Applicative ((<$>), (<*>))
import Control.Monad.Trans (lift)
import Data.Foldable (foldlM)
import Data.List (elemIndex)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Random (RVarT, RVar, normalT)

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
  
