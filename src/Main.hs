{-# LANGUAGE FlexibleInstances #-}
module Main where

import Debug.Trace (trace, traceShow)
import Control.Monad (liftM)
import Control.Applicative ((<$>), (<*>))
import Data.Map (Map, (!))
import qualified Data.Map as Map
import System.Environment (getArgs)
import qualified Text.JSON as JSON

import Quipp.BayesNet
import Quipp.ExpFam
import Quipp.Factor
import Quipp.GraphBuilder
import Quipp.Util
import Quipp.Value
import Quipp.Vmp



zip1_2 :: [a] -> [(b, c)] -> [(a, b, c)]
zip1_2 xs yzs = zipWith (\x (y, z) -> (x, y, z)) xs yzs

decodeExpFam :: JSON.JSValue -> ExpFam Value
decodeExpFam ef = case ef !: "type" of
  "gaussian" -> gaussianValueExpFam
  "bernoulli" -> boolValueExpFam
  "categorical" -> categoricalValueExpFam (ef !: "n")

getResult :: JSON.Result a -> a
getResult (JSON.Ok a) = a
getResult (JSON.Error str) = error $ "Error decoding: " ++ str

decodeJSON :: JSON.JSON a => String -> a
decodeJSON = getResult . JSON.decode

infixl 9 !:
(!:) :: JSON.JSON b => JSON.JSValue -> String -> b
(JSON.JSObject obj) !: key = case Map.lookup key (Map.fromList (JSON.fromJSObject obj)) of
  Nothing -> error ("Key not found: " ++ key ++ " in " ++ show obj)
  Just result -> case JSON.readJSON result of
    JSON.Ok a -> a
    JSON.Error str -> error $ "Error looking up " ++ key ++ " in " ++ show obj ++ ": " ++ str
other !: key = error ("Not object: " ++ show other)

decodeTemplate :: String -> FactorGraphTemplate Value
decodeTemplate str = makeFactorGraphTemplate
    (map convVar (m !: "vars"))
    (zip1_2 [0..] $ map convRandFun (m !: "randFuns"))
    (zip1_2 [0..] $ map convFactor (m !: "factors"))
  where m = decodeJSON str
        convVar (i, ef) = (i, decodeExpFam ef)
        convRandFun rf =
          (decodeExpFam (rf !: "resExpFam"),
           map decodeExpFam (rf !: "argExpFams"))
        convFactor fac =
          let facinfo = fac !: "factor" in
          (case facinfo !: "type" of
             "randFun" -> Right (facinfo !: "id")
             "uniformCategorical" ->
               let n = facinfo !: "n" in
               Left $ expFamFactor (categoricalValueExpFam n) [] (replicate (n - 1) 0.0, replicate (n-1) [])
             "normal" ->
               let mean = facinfo !: "mean"
                   stdev = facinfo !: "stdev"
              in Left $ expFamFactor gaussianValueExpFam [] ([mean / stdev^2, -1 / (2 * stdev^2)], [[]])
             "constant" -> Left $ constFactor (decodeExpFam (facinfo !: "expFam")) $ case facinfo !: "expFam" !: "type" of
               "gaussian" -> DoubleValue (facinfo !: "value")
               "bernoulli" -> BoolValue (facinfo !: "value")
               "categorical" -> CategoricalValue (facinfo !: "value")
             other -> error $ "Unknown factor type: " ++ other

           , fac !: "argVarIds")

decodeParams :: String -> FactorGraphParams
decodeParams = decodeJSON

encodeParams :: FactorGraphParams -> String
encodeParams = JSON.encode

makeJSObject :: [(String, JSON.JSValue)] -> JSON.JSValue
makeJSObject = JSON.JSObject . JSON.toJSObject

instance JSON.JSON Value where
  readJSON js = case js !: "type" of
    "double" -> return $ DoubleValue (js !: "value")
    "bool" -> return $ BoolValue (js !: "value")
    "categorical" -> return $ CategoricalValue (js !: "value")
  showJSON (DoubleValue d) = makeJSObject [("type", JSON.showJSON "double"), ("value", JSON.showJSON d)]
  showJSON (BoolValue b) = makeJSObject [("type", JSON.showJSON "bool"), ("value", JSON.showJSON b)]
  showJSON (CategoricalValue c) = makeJSObject [("type", JSON.showJSON "categorical"), ("value", JSON.showJSON c)]


instance JSON.JSON (Likelihood Value) where
  readJSON x = case getResult $ JSON.readJSON x of
    Left v -> JSON.Ok $ KnownValue v
    Right np -> JSON.Ok $ NatParam np
  showJSON (KnownValue v) = JSON.showJSON (Left v :: Either Value [Double])
  showJSON (NatParam np) = JSON.showJSON (Right np :: Either Value [Double])


decodeState :: String -> FactorGraphState Value
decodeState = decodeJSON

encodeState :: FactorGraphState Value -> String
encodeState = JSON.encode

pyRandTemplateParams :: FactorGraphTemplate Value -> IO FactorGraphParams
pyRandTemplateParams templ = sampleRVar $ randTemplateParams 10.0 templ

pySampleBayesNet :: FactorGraphTemplate Value -> FactorGraphParams -> IO (FactorGraphState Value)
pySampleBayesNet templ params =
  sampleRVar $ liftM (fmap KnownValue) $ sampleBayesNet (instantiateTemplate templ params)

type FST = (FactorGraphState Value, FactorGraphParams)

pyInitEM :: FactorGraphTemplate Value -> IO FST
pyInitEM templ = do
  params <- sampleRVar $ randTemplateParams 0.001 templ
  return (initFactorGraphState (instantiateTemplate templ params), params)


pyStepEM :: FactorGraphTemplate Value -> FST -> IO FST
pyStepEM templ (state, params) = sampleRVar $ do
  let factorGraph = instantiateTemplate templ params
  newStates <- sampleRVarTWith (\(Just x) -> return x) $ iterateM 20 (stepMH factorGraph) state
  let params' = updateTemplateParams templ params [(1.0, s) | s <- takeEvery 1 (tail newStates)]
  return (last newStates, params')


readTemplate :: String -> IO (FactorGraphTemplate Value)
readTemplate f = decodeTemplate <$> readFile f

readParams :: String -> IO FactorGraphParams
readParams f = decodeParams <$> readFile f

writeParams :: String -> FactorGraphParams -> IO ()
writeParams f params = writeFile f (encodeParams params)

readState :: String -> IO (FactorGraphState Value)
readState f = decodeState <$> readFile f

writeState :: String -> FactorGraphState Value -> IO ()
writeState f state = writeFile f (encodeState state)

main = do
  args <- getArgs
  case args of
    ["randTemplateParams", templateFile, paramsFile] ->
      readTemplate templateFile >>= pyRandTemplateParams >>= writeParams paramsFile
    ["sampleBayesNet", templateFile, paramsFile, stateFile] -> do
      templ <- readTemplate templateFile
      params <- readParams paramsFile
      pySampleBayesNet templ params >>= writeState stateFile
    ["initEM", templateFile, stateFile, paramsFile] -> do
      templ <- readTemplate templateFile
      (state, params) <- pyInitEM templ
      writeState stateFile state
      writeParams paramsFile params
    ["stepEM", templateFile, stateFile, paramsFile] -> do
      templ <- readTemplate templateFile
      state <- readState stateFile
      params <- readParams paramsFile
      (state', params') <- pyStepEM templ (state, params)
      writeState stateFile state'
      writeParams paramsFile params'
    _ -> error ("Bad command " ++ show args)

