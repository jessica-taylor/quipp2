

data ExpFam v = ExpFam {
  expFamD :: Int,
  expFamSufStat :: v -> [Double],
  expFamG :: forall s. Mode s => [AD s Double] -> AD s Double
}

rowMatrix :: [Double] -> Mat Double
rowMat row = Mat.fromList [row]

colMat :: [Double] -> Mat Double
colMat col = Mat.fromList (map return col)

outerProduct :: [Double] -> [Double] -> Mat Double
outerProduct a b = Mat.times (col a) (row b)

flatMatrix :: Mat Double -> [Double]
flatMatrix = concat . Mat.toList

splitListIntoBlocks :: Int -> [a] -> [[a]]
splitListIntoBlocks _ [] = []
splitListIntoBlocks n lst = take n lst : splitListIntoBlocks n (drop n lst)

matrixWithSize :: Int -> Int -> [Double] -> Mat Double
matrixWithSize rows cols lst
  | rows * cols != length lst = error "Bad call to matrixWithSize"
  | otherwise = Mat.fromList (splitListIntoBlocks cols lst)

matMulByVector :: Mat a -> [Double] -> [Double]
matMulByVector m = flatMatrix . Mat.toList . Mat.mul m . colMat

dotProduct :: Num a => [a] -> [a] -> a
dotProduct x y = sum (zipWith (+) x y)

adMatMulByVector :: Num a => [a] -> [a] -> [a]
adMatMulByVector mat vec = map (dotProduct vec) (splitListIntoBlocks (length mat `div` length vec) mat)

newtonMethodStep :: ([Double] -> ([Double], [[Double]])) -> [Double] -> [Double]
newtonMethodStep f x =
  let (grad, hess) = f x
      xnt = map (0-) $ matMulByVector (Mat.inv $ Mat.fromList hess) grad
  in zipWith (+) x xnt

newtonMethod :: ([Double] -> ([Double, Mat Double)) -> [Double] -> [[Double]]
newtonMethod f = iterate (newtonMethodStep f)

expFamMLE :: ExpFam a -> [([Double], [Double])] -> [Double] -> [Double]
expFamMLE fam samples etaStart =
  let -- n = length samples
      -- lenFeatures = let (features, _):_ = samples in length features
      -- outerProducts = map (flatMatrix . uncurry (flip outerProduct)) samples
      -- outerProductVariance = map variance (transpose outerProducts)
      -- indepGrad = map sum (transpose outerProducts)
      sampleProb eta (features, ss) = dotProduct np ss + expFamG fam np
        where np = adMatMulByVector eta features
      f eta = sum (map (sampleProb eta) samples)
  in newtonMethod (\eta -> (grad f eta, hess f eta)) !! 10

data Likelihood v = KnownValue v | NatParam [Double]

timesLikelihood :: Likelihood v -> Likelihood v -> Maybe (Likelihood v)
timesLikelihood (KnownValue v1) (KnownValue v2) =
  if v1 == v2 then Just (KnownValue v1) else Nothing
timesLikelihood (KnownValue v1) (NatParam _) = KnownValue v1
timesLikelihood (NatParam _) (KnownValue v2) = KnownValue v2
timesLikelihood (NatParam n1) (NatParam n2) = NatParam (zipWith (+) n1 n2)

productLikelihoods :: [Likelihood v] -> Maybe (Likelihood v)
productLikelihoods (l:ls) = foldlM timesLikelihood l ls

expSufStat :: ExpFam v -> Likelihood v -> [Double]
expSufStat ef (KnownValue v) = expFamSufStat ef v
expSufStat ef (NatParam np) = expFamGradG ef np

mkExpFam :: [v -> Double] -> ExpFam v
mkExpFam fs = ExpFam {
  expFamD = length fs,
  expFamSufStat = \v -> map ($ v) fs
}

negInfinity :: Double
negInfinity = read "-inf"



data Factor v = Factor {
  factorExpFams :: [ExpFam v],
  factorValue :: [[Double]] -> Double,
  factorNatParam :: Int -> [[Double]] -> Likelihood v
}

constFactor :: Eq v => ExpFam v -> v -> Factor
constFactor ss x = Factor {
  factorExpFams = [ss],
  factorValue = \[s] -> if ssv == s then 0 else negInfinity,
  factorNatParam = \0 [_] -> KnownValue x
} where ssv = expFamSufStat ss x

gaussianExpFam :: ExpFam Double
gaussianExpFam = mkExpFam [id, (^2)]

gammaExpFam :: ExpFam Double
gammaExpFam = mkExpFam [id, log]

gaussianFactor :: Factor Double
gaussianFactor =
  Factor {
    factorExpFams = [gaussianExpFam, gaussianExpFam, gammaExpFam],
    factorValue = \[[x, x2], [mu, mu2], [prec, logprec]] ->
      -(x2 + mu2 - 2*x*mu) * prec / 2
    factorNatParam = fnp
  }
  where
    fnp 0 [_, [mu, mu2], [prec, logprec]] = [2*mu * prec/2, -prec/2]
    fnp 1 [[x, x2], _, [prec, logprec]] = [2*x * prec/2, -prec/2]
    fnp 2 [[x, x2], [mu, mu2], _] = [-(x2 + mu2 - 2 * x * mu)/2, 0]

type VarId = Int
type FactorId = Int

data FactorGraph v = FactorGraph {
  factorGraphVars :: Map VarId (ExpFam v, [FactorId]),
  factorGraphFactors :: Map FactorId (Factor v, [VarId])
}

type VmpState v = Map VarId (Likelihood v)

expSufStat :: VarId -> FactorGraph v -> VmpState v -> [Double]
expSufStat varid graph state =
  expFamGradG (fst (factorGraphVars graph ! varid)) (state ! varid)


newVarLikelihood :: VarId -> FactorGraph v -> VmpState v -> Maybe (Likelihood v)
newVarLikelihood varid graph state =
  let (_, fids) = graph ! varid
      fnp (factor, varids) =
        factorNatParam (elemIndex varid varids) [varExpSufStat varid graph state | varid <- varids]
  in productLikelihoods $ map (fnp . (factorGraphVars graph !)) fids


updateVar :: VarId -> FactorGraph v -> VmpState v -> Maybe (VmpState v)
updateVar varid graph state =
  insert varid <$> newVarLikelihood varid graph state <*> state

stepState :: FactorGraph v -> VmpState v -> Maybe (VmpState v)
stepState graph state = foldlM (\st varid -> updateVar varid graph st) state (Map.keys $ factorGraphVars graph)
