{-# LANGUAGE FlexibleInstances #-}
module Main where

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

decodeExpFam :: String -> ExpFam Value
decodeExpFam "gaussian" = gaussianValueExpFam
decodeExpFam "bernoulli" = boolValueExpFam

getResult :: JSON.Result a -> a
getResult (JSON.Ok a) = a
getResult (JSON.Error str) = error str

decodeJSON :: JSON.JSON a => String -> a
decodeJSON = getResult . JSON.decode

infixl 9 !:
(!:) :: JSON.JSON b => JSON.JSValue -> String -> b
(JSON.JSObject obj) !: key = case Map.lookup key (Map.fromList (JSON.fromJSObject obj)) of
  Nothing -> error ("Key not found: " ++ key ++ " in " ++ show obj)
  Just result -> getResult $ JSON.readJSON result

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
             "constant" -> Left $ constFactor (decodeExpFam (facinfo !: "expFam")) $ case facinfo !: "expFam" of
               "gaussian" -> DoubleValue (facinfo !: "value")
               "bernoulli" -> BoolValue (facinfo !: "value"),
           fac !: "argVarIds")

decodeParams :: String -> FactorGraphParams
decodeParams = decodeJSON

encodeParams :: FactorGraphParams -> String
encodeParams = JSON.encode

instance JSON.JSON Value where
  readJSON js@(JSON.JSRational _ _) = fmap DoubleValue $ JSON.readJSON js
  readJSON js@(JSON.JSBool _) = fmap BoolValue $ JSON.readJSON js
  showJSON (DoubleValue d) = JSON.showJSON d
  showJSON (BoolValue b) = JSON.showJSON b

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
  newStates <- sampleRVarTWith (\(Just x) -> return x) $ iterateM 10 (stepMH factorGraph) state
  params' <- updateTemplateParamsMH templ params [(1.0, s) | s <- takeEvery 1 (tail newStates)]
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
      print stateFile
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

