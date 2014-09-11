

data Type = DoubleType deriving (Eq, Ord, Show)

data Value = DoubleValue Double deriving (Eq, Ord, Show)

getType :: Value -> Type
getType (DoubleValue _) = DoubleType

data ExpFam = ExpFam {
  expFamD :: Int,
  expFamSufStat :: Value -> [Double],
  expFamG :: [Double] -> Double,
  expFamGradG :: [Double] -> [Double]
}

data Likelihood = KnownValue Value | NatParam [Double]

timesLikelihood :: Likelihood -> Likelihood -> Maybe Likelihood
timesLikelihood (KnownValue v1) (KnownValue v2) =
  if v1 == v2 then Just (KnownValue v1) else Nothing
timesLikelihood (KnownValue v1) (NatParam _) = KnownValue v1
timesLikelihood (NatParam _) (KnownValue v2) = KnownValue v2
timesLikelihood (NatParam n1) (NatParam n2) = NatParam (zipWith (+) n1 n2)

productLikelihoods :: [Likelihood] -> Maybe Likelihood
productLikelihoods (l:ls) = foldlM timesLikelihood l ls

expSufStat :: ExpFam -> Likelihood -> [Double]
expSufStat ef (KnownValue v) = expFamSufStat ef v
expSufStat ef (NatParam np) = expFamGradG ef np

data Factor = Factor {
  factorExpFams :: [ExpFam],
  factorValue :: [[Double]] -> Double,
  factorNatParam :: Int -> [[Double]] -> Likelihood
}

mkExpFam :: [Value -> Double] -> ExpFam
mkExpFam fs = ExpFam {
  expFamD = length fs,
  expFamSufStat = \v -> map ($ v) fs

negInfinity :: Double
negInfinity = read "-inf"

constFactor :: ExpFam -> Value -> Factor
constFactor ss x = Factor {
  factorExpFams = [ss],
  factorValue = \[s] -> if ssv == s then 0 else negInfinity,
  factorNatParam = \0 [_] -> KnownValue x
} where ssv = expFamSufStat ss x

gaussianExpFam :: ExpFam
gaussianExpFam = mkExpFam [\DoubleValue x -> x, \DoubleValue x -> x^2]

gammaExpFam :: ExpFam
gammaExpFam = mkExpFam [\DoubleValue x -> x, \DoubleValue x -> log x]

gaussianFactor :: Factor
gaussianFactor =
  Factor {
    factorExpFams = [gaussianExpFam, gaussianExpFam, gammaExpFam],
    factorValue = \[[x, x2], [mu, mu2], [prec, logprec]] ->
      (x2 + mu2 - 2*x*mu) * prec / 2
    factorNatParam = fnp
  }
  where
    fnp 0 [_, [mu, mu2], [prec, logprec]] = [, ???]

type VarId = Int
type FactorId = Int

data FactorGraph = FactorGraph {
  factorGraphVars :: Map VarId (ExpFam, [FactorId]),
  factorGraphFactors :: Map FactorId (Factor, [VarId])
}

type VmpState = Map VarId Likelihood

expSufStat :: VarId -> FactorGraph -> VmpState -> [Double]
expSufStat varid graph state =
  expFamGradG (fst (factorGraphVars graph ! varid)) (state ! varid)
  

newVarLikelihood :: VarId -> FactorGraph -> VmpState -> Likelihood
newVarLikelihood varid graph state =
  let (_, fids) = graph ! varid
      fnp (factor, varids) =
        factorNatParam (elemIndex varid varids) (map (...))
      natparams = map (fnp . (factorGraphVars graph !)) fids
  

updateVar :: VarId -> VmpState -> VmpState
updateVar varid state =
  


