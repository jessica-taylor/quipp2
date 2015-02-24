{-# LANGUAGE TupleSections #-}

module Quipp.Factor (
  Factor(Factor, factorExpFams, factorLogValue, factorNatParam, factorBayesNetOutput),
  promoteFactor, constFactor, expFamFactor,
  VarId, RandFunId, FactorId, FactorGraph(FactorGraph, factorGraphVars, factorGraphFactors),
  FactorGraphTemplate(FactorGraphTemplate, factorGraphTemplateRandFunctions, factorGraphTemplateVars, factorGraphTemplateFactors),
  makeFactorGraphTemplate, instantiateTemplate, instantiateTemplateWithVariableParameters,
  FactorGraphState, initFactorGraphState, varExpSufStat, newVarLikelihood,
  factorExpLogValue,
  FactorGraphParams, randTemplateParams, updateTemplateParams, updateTemplateParamsMH,
  ifThenElseFactor,
  notFactor) where

import Control.Arrow ((>>>))
import Control.Monad (liftM, replicateM)
import Control.Monad.State.Class (get, put)
import Control.Monad.State.Lazy (evalState)
import Debug.Trace
import Data.List (elemIndex)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Random (RVar, normal)
import Numeric.AD (grad)

import Quipp.Value
import Quipp.ExpFam
import Quipp.Util

data Factor v = Factor {
  factorExpFams :: [ExpFam v],
  factorLogValue :: [Likelihood v] -> Double,
  factorNatParam :: Int -> [Likelihood v] -> Likelihood v,
  factorBayesNetOutput :: Maybe (Bool, Int)
}

instance Show (Factor v) where
  show f = "<factor " ++ show (factorExpFams f) ++ ">"

flipPair (a, b) = (b, a)

promoteFactor :: (v -> u, u -> v) -> Factor v -> Factor u
promoteFactor fs fac = Factor {
  factorExpFams = map (promoteExpFam fs) (factorExpFams fac),
  factorLogValue = \ls -> factorLogValue fac (map (promoteLikelihood (flipPair fs)) ls),
  factorNatParam = \i ls -> promoteLikelihood fs (factorNatParam fac i (map (promoteLikelihood (flipPair fs)) ls)),
  factorBayesNetOutput = factorBayesNetOutput fac
}

constFactor :: Eq v => ExpFam v -> v -> Factor v
constFactor ss x = Factor {
  factorExpFams = [ss],
  factorLogValue = \[val] -> if val == KnownValue x then 0 else negInfinity,
  factorNatParam = \0 [_] -> KnownValue x,
  factorBayesNetOutput = Just (True, 0)
}

-- gaussianFactor :: Factor Double
-- gaussianFactor =
--   Factor {
--     factorExpFams = [gaussianExpFam, gaussianExpFam, gammaExpFam],
--     factorLogValue = \[[x, x2], [mu, mu2], [prec, logprec]] ->
--       -(x2 + mu2 - 2*x*mu) * prec / 2,
--     factorNatParam = NatParam .: fnp
--   }
--   where
--     fnp 0 [_, [mu, mu2], [prec, logprec]] = [2*mu * prec/2, -prec/2]
--     fnp 1 [[x, x2], _, [prec, logprec]] = [2*x * prec/2, -prec/2]
--     fnp 2 [[x, x2], [mu, mu2], _] = [-(x2 + mu2 - 2 * x * mu)/2, 0]



-- TODO: something is fishy here.  Things get flipped when they shouldn't.
expFamFactor :: ExpFam v -> [ExpFam v] -> Params Double -> Factor v
expFamFactor ef argExpFams eta@(etaBase, etaWeights) =
  Factor {
    factorExpFams = ef:argExpFams,
    -- TODO filter
    factorLogValue = expSufStatAndFeatures >>> \(ss, feats) -> expFamLogProbability ef eta feats ss,
    factorNatParam = \i ls -> NatParam (fnp i (expSufStatAndFeatures ls)),
    factorBayesNetOutput = Just (False, 0)
  }
  where expSufStatAndFeatures (likelihood:argsLikelihoods) = (expSufStat ef likelihood, concat [expFamSufStatToFeatures aef (expSufStat aef l) | (l, aef) <- zip argsLikelihoods argExpFams])
        fnp 0 (_, feats) = getNatParam ef eta feats
        fnp n (ss, feats) =
          let gradProbNp = grad (\np -> dotProduct np (map fromDouble ss) - expFamG ef np) $ getNatParam ef eta feats
              minFeatureIndex = sum $ map expFamFeaturesD $ take (n-1) argExpFams
              thisArgDim = expFamFeaturesD (argExpFams !! (n-1))
              relevantWeights = map (take thisArgDim . drop minFeatureIndex) etaWeights
          in expFamFeaturesToSufStat (argExpFams !! (n-1)) $ matMulByVector (transpose relevantWeights) gradProbNp

listInsertAt :: Int -> a -> [a] -> [a]
listInsertAt i x l = take i l ++ [x] ++ drop (i+1) l

paramsFromDouble :: RealFloat a => Params Double -> Params a
paramsFromDouble (base, weights) = (map fromDouble base, map (map fromDouble) weights)

expFamWithParamsFactor :: ExpFam Value -> [ExpFam Value] -> Factor Value
expFamWithParamsFactor ef argExpFams =
  Factor {
    factorExpFams = ef : argExpFams ++ replicate (expFamD ef + expFamFeaturesD ef * sum (map expFamFeaturesD argExpFams)) gaussianValueExpFam,
    factorLogValue = flv,
    factorNatParam = NatParam .: fnp
  }
  where splitSufStats (xLike:rest) =
          let (argLikes, rest') = splitAt (length argExpFams) rest
              (etaBaseLikes, etaWeightsLikes) = splitAt (expFamD ef) rest'
          in (expSufStat ef xLike,
              concat [expFamSufStatToFeatures aef (expSufStat aef l) | (l, aef) <- zip argLikes argExpFams],
              map (expSufStat gaussianValueExpFam) etaBaseLikes,
              map (expSufStat gaussianValueExpFam) etaWeightsLikes)
        flv likelihoods =
          let (ss, argExpFeats, etaBaseSs, etaWeightsSs) = splitSufStats likelihoods
              expEta = (map head etaBaseSs, splitListIntoBlocks (expFamFeaturesD ef) (map head etaWeightsSs))
          in expFamLogProbability ef expEta argExpFeats ss
        fnp i sss =
          let (ss, argExpFeats, etaBaseSs, etaWeightsSs) = splitSufStats sss
              expEta = (map head etaBaseSs, splitListIntoBlocks (expFamFeaturesD ef) (map head etaWeightsSs))
          in if i == 0
             then getNatParam ef expEta argExpFeats
             else let i' = i - 1 in
             if i' < length argExpFams
             then grad (\afs -> expFamLogProbability ef (paramsFromDouble expEta) afs (map fromDouble ss)) argExpFeats
             else let i'' = i' - length argExpFams in
             if i'' < expFamD ef
             then let f :: RealFloat a => a -> a
                      f p = expFamLogProbability ef (listInsertAt i'' p (map fromDouble $ fst expEta), map (map fromDouble) $ snd expEta) (map fromDouble argExpFeats) (map fromDouble ss)
                      (_, n1, n2) = quadApproximation f (fst expEta !! i'')
                  in [n1, n2]
             else let i''' = i'' - length (fst expEta)
                      f :: RealFloat a => a -> a
                      f p = expFamLogProbability ef (map fromDouble $ fst expEta, splitListIntoBlocks (expFamFeaturesD ef) (listInsertAt i''' p (map (fromDouble . head) etaWeightsSs))) (map fromDouble argExpFeats) (map fromDouble ss)
                      (_, n1, n2) = quadApproximation f (head $ etaWeightsSs !! i''')
                  in [n1, n2]

type VarId = Int
type FactorId = Int

data FactorGraph v = FactorGraph {
  factorGraphVars :: Map VarId (ExpFam v, [FactorId]),
  factorGraphFactors :: Map FactorId (Factor v, [VarId])
} deriving Show

type RandFunId = Int

data FactorGraphTemplate v = FactorGraphTemplate {
  factorGraphTemplateVars :: Map VarId (ExpFam v, [FactorId]),
  factorGraphTemplateRandFunctions :: Map RandFunId (ExpFam v, [ExpFam v], [FactorId]),
  factorGraphTemplateFactors :: Map FactorId (Either (Factor v) RandFunId, [VarId])
} deriving Show

makeFactorGraphTemplate :: [(VarId, ExpFam v)] -> [(RandFunId, ExpFam v, [ExpFam v])] -> [(FactorId, Either (Factor v) RandFunId, [VarId])] -> FactorGraphTemplate v
makeFactorGraphTemplate vars randfuns factors = traceShow (vars, fgv) $ FactorGraphTemplate (Map.fromList fgv) (Map.fromList fgrf) (Map.fromList fgf)
  where fgv = [(varid, (ef, [factorid | (factorid, _, vars) <- factors, elem varid vars])) | (varid, ef) <- vars]
        fgrf = [(rfid, (ef, featureEfs, [factorid | (factorid, Right rfid', _) <- factors, rfid' == rfid])) | (rfid, ef, featureEfs) <- randfuns]
        fgf = [(factorid, (fac, vars)) | (factorid, fac, vars) <- factors]

type FactorGraphParams = Map RandFunId (Params Double)

instantiateTemplate :: FactorGraphTemplate v -> FactorGraphParams -> FactorGraph v
instantiateTemplate templ params =
  FactorGraph {
    factorGraphVars = factorGraphTemplateVars templ,
    factorGraphFactors = Map.mapWithKey fixFactor (factorGraphTemplateFactors templ)
  }
  where fixFactor _ (Left f, vars) = (f, vars)
        fixFactor factorid (Right randfun, var:vars) =
          (expFamFactor (getExpFam var) (map getExpFam vars) (params ! randfun), var:vars)
        getExpFam var = fst (factorGraphTemplateVars templ ! var)

instantiateTemplateWithVariableParameters :: FactorGraphTemplate Value -> (FactorGraph Value, Map RandFunId ([VarId], [[VarId]]))
instantiateTemplateWithVariableParameters templ =
  let newVarId = do
        cur <- get
        put (cur + 1)
        return cur
      varIdsForParams (rfid, (ef, aefs, _)) = do
        base <- replicateM (expFamD ef) newVarId
        weights <- replicateM (expFamFeaturesD ef) $ replicateM (sum $ map expFamFeaturesD aefs) newVarId
        return (rfid, (base, weights))
      varIdsForAllParams = liftM Map.fromList $ mapM varIdsForParams $ Map.toList (factorGraphTemplateRandFunctions templ)
      paramVarIdsMap = evalState varIdsForAllParams (1 + maximum (Map.keys (factorGraphTemplateVars templ)))
      allParamVarIds = do
        (base, weights) <- Map.elems paramVarIdsMap
        base ++ concat weights
      factorsForRandFunId rfid = [factorid | (factorid, ((Right rfid'), _)) <- Map.toList (factorGraphTemplateFactors templ), rfid == rfid']
      fixFactor _ (Left f, vars) = (f, vars)
      fixFactor factorid (Right rfid, var:vars) =
        let (base, weights) = paramVarIdsMap ! rfid
        in (expFamWithParamsFactor (getExpFam var) (map getExpFam vars), var : vars ++ base ++ concat weights)
      getExpFam var = fst (factorGraphTemplateVars templ ! var)
  in (FactorGraph {
       factorGraphVars = Map.fromList $ Map.toList (factorGraphTemplateVars templ) ++ do
         (rfid, (base, weights)) <- Map.toList paramVarIdsMap
         let factors = factorsForRandFunId rfid
         varid <- base ++ concat weights
         return (varid, (gaussianValueExpFam, factors)),
       factorGraphFactors = Map.mapWithKey fixFactor (factorGraphTemplateFactors templ)
     }, paramVarIdsMap)


type FactorGraphState v = Map VarId (Likelihood v)

initFactorGraphState :: FactorGraph v -> FactorGraphState v
initFactorGraphState g = fmap (\(ef, _) -> NatParam $ replicate (expFamD ef) 0.0) (factorGraphVars g)

independentSampleFactorGraphState :: FactorGraph v -> FactorGraphState v -> RVar (FactorGraphState v)
independentSampleFactorGraphState factorGraph = liftM Map.fromList . mapM sampleVar . Map.toList
  where sampleVar (id, likelihood) = do
          value <- sampleLikelihood (fst $ factorGraphVars factorGraph ! id) likelihood
          return (id, KnownValue value)

varExpSufStat :: FactorGraph v -> FactorGraphState v -> VarId -> [Double]
varExpSufStat graph state varid =
  expSufStat (fst (factorGraphVars graph ! varid)) (state ! varid)

varCovarianceSufStat :: FactorGraph v -> FactorGraphState v -> VarId -> [[Double]]
varCovarianceSufStat graph state varid =
  covarianceSufStat (fst (factorGraphVars graph ! varid)) (state ! varid)

varExpFeatures :: FactorGraph v -> FactorGraphState v -> VarId -> [Double]
varExpFeatures graph state varid =
  let ef = fst (factorGraphVars graph ! varid)
  in expFamSufStatToFeatures ef $ varExpSufStat graph state varid

varCovarianceFeatures graph state varid =
  let ef = fst (factorGraphVars graph ! varid)
  in expFamSufStatToFeatures ef $ map (expFamSufStatToFeatures ef) $ varCovarianceSufStat graph state varid

factorExpLogValue :: FactorGraph v -> FactorGraphState v -> FactorId -> Double
factorExpLogValue graph state factorid =
  let (factor, varids) = factorGraphFactors graph ! factorid
  in factorLogValue factor $ map (state !) varids

newVarLikelihood :: Eq v => FactorGraph v -> FactorGraphState v -> VarId -> Maybe (Likelihood v)
newVarLikelihood graph state varid =
  let (_, fids) = factorGraphVars graph ! varid
      fnp (factor, varids) =
        factorNatParam factor (fromJust $ elemIndex varid varids) $ map (state !) varids
  in productLikelihoods $ map (fnp . (factorGraphFactors graph !)) fids

randTemplateParams :: Double -> FactorGraphTemplate v -> RVar FactorGraphParams
randTemplateParams stdev = fmap Map.fromList . mapM getParam . Map.toList . factorGraphTemplateRandFunctions
  where getParam (rfid, (ef, featureEfs, _)) = do
          base <- expFamRandomNatParam ef
          weights <- replicateM (expFamFeaturesD ef) $ replicateM (sum $ map expFamFeaturesD featureEfs) (normal 0.0 stdev)
          return (rfid, (base, weights))

updateTemplateParams :: FactorGraphTemplate v -> FactorGraphParams -> [(Double, FactorGraphState v)] -> FactorGraphParams
updateTemplateParams template origParams states = Map.mapWithKey updateParam origParams
  where origGraph = instantiateTemplate template origParams
        updateParam randFunId origParam =
          let (ef, featureEfs, factorIds) = factorGraphTemplateRandFunctions template ! randFunId
              factorValues factorId weight state =
                let (_, svarid:fvarids) = factorGraphTemplateFactors template ! factorId
                in (weight, concat (map (varExpFeatures origGraph state) fvarids),
                    varExpSufStat origGraph state svarid)
          in expFamMLE ef [factorValues factorId weight state | factorId <- factorIds, (weight, state) <- states] origParam !! 30

updateTemplateParamsMH :: FactorGraphTemplate v -> FactorGraphParams -> [(Double, FactorGraphState v)] -> RVar FactorGraphParams
updateTemplateParamsMH template origParams states = liftM Map.fromList $ mapM updateParam $ Map.toList origParams
  where origGraph = instantiateTemplate template origParams
        updateParam (randFunId, origParam) =
          let (ef, featureEfs, factorIds) = factorGraphTemplateRandFunctions template ! randFunId
              factorValues factorId weight state =
                let (_, svarid:fvarids) = factorGraphTemplateFactors template ! factorId
                in (weight, concat (map (varExpFeatures origGraph state) fvarids),
                    varExpSufStat origGraph state svarid)
          in do
            paramsList <- expFamMH ef [factorValues factorId weight state | factorId <- factorIds, (weight, state) <- states] origParam
            return (randFunId, paramsList !! 3)

notLikelihood :: Likelihood Value -> Likelihood Value
notLikelihood (KnownValue (BoolValue False)) = KnownValue (BoolValue True)
notLikelihood (KnownValue (BoolValue True)) = KnownValue (BoolValue False)
notLikelihood (NatParam [np]) = NatParam [-np]


notFactor :: Factor Value
notFactor = Factor {
    factorExpFams = [boolValueExpFam, boolValueExpFam],
    factorLogValue = \[ly, lx] -> expFamCrossEntropy boolValueExpFam ly (notLikelihood lx),
    factorNatParam = fnp,
    factorBayesNetOutput = Just (True, 0)
  }
  where fnp 0 [_, lx] = notLikelihood lx
        fnp 1 [ly, _] = notLikelihood ly

-- logOddsToProbability x = exp (x - logSumExp [0, x])

-- TODO: get this to work with gibbs sampling.  Need support for deterministic
-- functions.
ifThenElseFactor :: ExpFam Value -> Factor Value
ifThenElseFactor ef = Factor {
    factorExpFams = [ef, boolValueExpFam, ef, ef],
    factorLogValue = \[lx, lc, la, lb] ->
      let aCrossEntropy = expFamCrossEntropy ef lx la
          bCrossEntropy = expFamCrossEntropy ef lx lb
      in case lc of
        KnownValue (BoolValue False) -> aCrossEntropy
        KnownValue (BoolValue True) -> bCrossEntropy
        NatParam _ -> let [p] = expSufStat ef lc in logSumExp [log (1-p) + aCrossEntropy, log p + bCrossEntropy],
    factorNatParam = fnp,
    factorBayesNetOutput = Just (True, 0)
  }
  where fnp 0 [_, lc, la, lb] = case lc of
          KnownValue (BoolValue False) -> la
          KnownValue (BoolValue True) -> lb
          NatParam lp ->
            let [p] = expSufStat ef (NatParam lp)
                ex = [(1 - p) * a + p * b | (a, b) <- zip (expSufStat ef la) (expSufStat ef lb)]
            in expFamSufStatToLikelihood ef ex
        fnp 1 [lx, _, la, lb] =
          let aCrossEntropy = expFamCrossEntropy ef lx la
              bCrossEntropy = expFamCrossEntropy ef lx lb
          in NatParam [aCrossEntropy - bCrossEntropy]
        fnp 2 [lx, lc, _, lb] = case (lx, lc) of
          (_, KnownValue (BoolValue True)) -> NatParam $ replicate (expFamD ef) 0
          -- TODO: reasonable?
          (KnownValue xv, _) -> KnownValue xv
          (NatParam xp, NatParam lp) ->
            let [p] = expSufStat ef (NatParam lp) in NatParam $ map (*(1 - p)) xp
        fnp 3 [lx, lc, la, _] = case (lx, lc) of
          (_, KnownValue (BoolValue False)) -> NatParam $ replicate (expFamD ef) 0
          -- TODO: reasonable?
          (KnownValue xv, _) -> KnownValue xv
          (NatParam xp, NatParam lp) ->
            let [p] = expSufStat ef (NatParam lp) in NatParam $ map (*p) xp
