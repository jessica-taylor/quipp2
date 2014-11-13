module Quipp.BayesNet where

import Debug.Trace
import Data.Foldable (foldlM)
import Data.Graph (topSort, graphFromEdges')
import Data.List (elemIndex)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Random (RVar)

import Quipp.ExpFam
import Quipp.Factor


varidToBayesNetFactor :: FactorGraph v -> VarId -> FactorId
varidToBayesNetFactor graph varid =
  case [fid | fid <- snd $ factorGraphVars graph ! varid,
              let (factor, varids) = factorGraphFactors graph ! fid,
              let Just (_, i) = factorBayesNetOutput factor,
              varids !! i == varid] of
    [uniqueFid] -> uniqueFid
    other -> error ("Not a bayes net: " ++ show varid ++ ", " ++ show other)



sampleBayesNet :: FactorGraph v -> RVar (Map VarId v)
sampleBayesNet graph =
  let (g, vertexToNode) = graphFromEdges' [
        ((), varid, [res | fid <- fids,
                           let (fac, fvarids) = factorGraphFactors graph ! fid,
                           let Just (_, i) = factorBayesNetOutput fac,
                           let res = fvarids !! i,
                           res /= varid]) |
        (varid, (_, fids)) <- Map.toList (factorGraphVars graph)]
      varidsInOrder = [varid | vertex <- topSort g, let ((), varid, _) = vertexToNode vertex]
      sampleNextVar state varid =
        let ef = fst $ factorGraphVars graph ! varid
            factorid = varidToBayesNetFactor graph varid
            (factor, varids) = factorGraphFactors graph ! factorid
            likelihood = factorNatParam factor (fromJust $ elemIndex varid varids) $ map (KnownValue . (state !)) varids
        in do
          samp <- sampleLikelihood ef likelihood
          return $ Map.insert varid samp state
  in foldlM sampleNextVar Map.empty varidsInOrder



