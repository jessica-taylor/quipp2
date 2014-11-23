{-# LANGUAGE NoMonomorphismRestriction #-}
module Quipp.Parser (toplevel) where

import Debug.Trace

import Control.Applicative ((<$>), (<*>))
import Data.Char
import Data.Map (Map)
import qualified Data.Map as Map
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim

import Quipp.TypeInference
import Quipp.Util
import Quipp.Value

keywords = ["data", "rec", "newtype", "let", "in", "case", "of", "def"]

wordChar = satisfy (\x -> isAlphaNum x || x == '_')

wordBreak = notFollowedBy wordChar

type AdtDefinition = (String, [String], [(String, [TypeExpr])])

varList :: [String]
varList = ["x_" ++ show i | i <- [0..]]

type ParseContext = Map String AdtDefinition

translateNonRecursiveAdtDefinition :: AdtDefinition -> Expr -> Expr
translateNonRecursiveAdtDefinition (name, params, cases) body =
  let pairExpr x y = AppExpr (AppExpr (VarExpr "pair") x) y
      leftExpr = AppExpr (VarExpr "left")
      rightExpr = AppExpr (VarExpr "right")
      getConstr i ts = foldr LambdaExpr (rightsAndLeft $ foldr pairExpr (VarExpr "unit") (map VarExpr vars)) vars
        where vars = take (length ts) varList
              rightsAndLeft | i == length cases - 1 = funPow i rightExpr
                            | otherwise = leftExpr . funPow i rightExpr
  in NewTypeExpr (name, params, foldr1 eitherType [foldr pairType (ConstTExpr "Unit") ts | (_, ts) <- cases])
      $ foldr (\(i, (constrName, ts)) -> DefExpr constrName (getConstr i ts)) body (zip [0..] cases)

recursiveAdtDefinitionToFunctor :: AdtDefinition -> AdtDefinition
recursiveAdtDefinitionToFunctor (name, params, cases) =
  let recVar = name ++ "_rec"
      fixCase (caseName, ts) = (caseName, map fixType ts)
      recType = foldl1 AppTExpr $ map VarTExpr (name:params)
      fixType t | t == recType = VarTExpr recVar
      fixType (AppTExpr fun arg) = AppTExpr (fixType fun) (fixType arg)
      fixType (ConstTExpr t) | t == name = error "Cannot handle polymorphic recursion"
      fixType other = other
  in (name, params ++ [recVar], map fixCase cases)

data PatternExpr = VarPExpr String | ConstrPExpr String [PatternExpr] deriving (Eq, Ord, Show)

data PrimPatternExpr = VarPPExpr String | UnitPPExpr | PairPPExpr PrimPatternExpr PrimPatternExpr | LeftPPExpr PrimPatternExpr | RightPPExpr PrimPatternExpr | NewtypeConstrPPExpr String PrimPatternExpr

toPrimPat :: (String -> AdtDefinition) -> PatternExpr -> PrimPatternExpr
toPrimPat _ (VarPExpr s) = VarPPExpr s
toPrimPat constrDef (ConstrPExpr constr fields) =
  let (adtName, _, adtCases) = constrDef constr
      caseIndex = fromJust $ findIndex ((== constr) . fst) adtCases
      leftsAndRight | caseIndex == length adtCases - 1 = funPow caseIndex LeftPPExpr
                    | otherwise = RightPPExpr . funPow caseIndex LeftPPExpr
  in NewtypeConstrPPExpr adtName $ leftsAndRight $ foldr PairPPExpr UnitPPExpr $ map (toPrimPat constrDef) fields

primPatImplies :: PrimPatternExpr -> PrimPatternExpr -> Bool
primPatImplies _ (VarPPExpr _) = True
primPatImplies (VarPPExpr _) _ = False
primPatImplies UnitPPExpr UnitPPExpr = True
primPatImplies (PairPPExpr a b) (PairPPExpr c d) = primPatImplies a c && primPatImplies b d
primPatImplies (LeftPPExpr a) (LeftPPExpr b) = primPatImplies a b
primPatImplies (RightPPExpr a) (RightPPExpr b) = primPatImplies a b
primPatImplies (NewtypeConstrPPExpr c a) (NewtypeConstrPPExpr c' b) = c == c' && primPatImplies a b
primPatImplies _ _ = False

-- TODO:  what if we match on Left a, then Right b, then c?
removeRedundantCases :: [(PrimPatternExpr, Expr)] -> [(PrimPatternExpr, Expr)]
removeRedundantCases cases = [(pat, body) | ((pat, body), prevPats) <- zip cases (inits (map fst cases)), not $ any (primPatImplies pat) prevPats]

type PrimPatternLens = [Bool]

lensToExpr :: PrimPatternLens -> Expr -> Expr
lensToExpr lens val = foldr (\l -> AppExpr (VarExpr (if l then "snd" else "fst"))) val lens

modifyLensExpr :: PrimPatternLens -> Expr -> Expr -> Expr
modifyLensExpr [] f x = AppExpr f x
modifyLensExpr (False:ls) f x =
  foldl1 AppExpr [VarExpr "pair", modifyLensExpr ls f (AppExpr (VarExpr "fst") x), AppExpr (VarExpr "snd") x]
modifyLensExpr (True:ls) f x =
  foldl1 AppExpr [VarExpr "pair", AppExpr (VarExpr "fst") x, modifyLensExpr ls f (AppExpr (VarExpr "snd") x)]

pointToExpandable :: PrimPatternExpr -> Maybe (PrimPatternLens, Maybe String)
pointToExpandable (LeftPPExpr _) = return ([], Nothing)
pointToExpandable (RightPPExpr _) = return ([], Nothing)
pointToExpandable (NewtypeConstrPPExpr c _) = return ([], Just c)
pointToExpandable (PairPPExpr first second) =
  search False first `mplus` search True second
  where search b p = do
    (lens, tag) <- pointToExpandable p
    return (b : lens, tag)
pointToExpandable other = Nothing

pointToAnyExpandable :: [PrimPatternExpr] -> Maybe PrimPatternLens
pointToAnyExpandable = foldl1 mplus . map pointToExpandable

partitionCase :: PrimPatternLens -> (PrimPatternExpr, Expr) -> ([(PrimPatternExpr, Expr)], [(PrimPatternExpr, Expr)])
partitionCase lens (VarPPExpr v, body) =
  let part f = [(VarPPExpr v, AppExpr (LambdaExpr v body) $ modifyLensExpr lens (VarExpr f) v)]
  in (part "left", part "right")
partitionCase [] (LeftPPExpr p, body) = ([(p, body)], [])
partitionCase [] (RightPPExpr p, body) = ([], [(p, body)])
partitionCase (False:l) (PairPPExpr f s, body) =
  let (fcasesl, fcasesr) = partitionCase l (f, body) in
      ([(PairPPExpr f' s, b) | (f', b) <- fcasesl],
       [(PairPPExpr f' s, b) | (f', b) <- fcasesr])
partitionCase (True:l) (PairPPExpr f s, body) =
  let (scasesl, scasesr) = partitionCase l (s, body) in
      ([(PairPPExpr f s', b) | (s', b) <- scasesl],
       [(PairPPExpr f s', b) | (s', b) <- scasesr])

partitionCases :: PrimPatternLens -> [(PrimPatternExpr, Expr)] -> ([(PrimPatternExpr, Expr)], [(PrimPatternExpr, Expr)])
partitionCases lens cases =
  let partCases = map (partitionCase lens) cases in (concat $ map fst partCases, concat $ map snd partCases)

expandNewtypeCase :: PrimPatternLens -> String -> (PrimPatternExpr, Expr) -> (PrimPatternExpr, Expr)
expandNewtypeCase lens constrName (VarPPExpr v, body) =
  (VarPPExpr v, AppExpr (LambdaExpr v body) $ modifyLensExpr lens (VarExpr constrName) v)
expandNewtypeCase [] constrName (NewtypeConstrPPExpr constrName' p, body)
  | constrName == constrName' = (p, body)
expandNewtypeCase (False:l) (PairPPExpr f s, body) =
  let (f', b) = expandNewtypeCase l f in (PairPPExpr f' s, body)
expandNewtypeCase (True:l) (PairPPExpr f s, body) =
  let (s', b) = expandNewtypeCase l s in (PairPPExpr f s', body)


casesToExpr :: Expr -> [(PrimPatternExpr, Expr)] -> Expr
casesToExpr ex cases =
  let cases' = removeRedundantCases cases in
  case pointToExpandable (map fst cases') of
    Nothing -> fullyExpandedMatch ex (fst cases')
    Just (lens, Nothing) ->
      let (leftCases, rightCases) = partitionCases lens cases'
          handler cs = LambdaExpr varname $ casesToExpr (modifyLensExpr lens (LambdaExpr varname2 (VarExpr varname)) ex) cs
      in foldl1 AppExpr [VarExpr "either", lensToExpr lens ex, handler leftCases, handler rightCases]
    Just (lens, Just ntname) ->
      let newCases = map (expandNewtypeCase lens) cases'
      in casesToExpr (modifyLensExpr lens (VarExpr ("un" ++ ntname)) ex) newCases

infixl 1 ^>>

(^>>) :: Monad m => m a -> m b -> m a
a ^>> b = do
  x <- a
  b
  return x

(>>++) :: Monad m => m [a] -> m [a] -> m [a]
a >>++ b = do
  x <- a
  y <- b
  return (x ++ y)

withWhitespace p = p ^>> spaces

spacedString = withWhitespace . string

withBreak p = p ^>> wordBreak ^>> spaces

stringWithBreak = withBreak . string


upperId = withBreak ((:) <$> satisfy isUpper <*> many wordChar)

lowerId = withBreak $ do
  id <- (:) <$> satisfy isLower <*> many wordChar
  if elem id keywords then fail "Keyword is not an ID" else return id

varTypeExpr = VarTExpr <$> lowerId

constTypeExpr = ConstTExpr <$> upperId

atomTypeExpr = varTypeExpr <|> constTypeExpr <|> withParens typeExpr

applicationTypeExpr = foldl1 AppTExpr <$> many1 atomTypeExpr

functionTypeExpr = foldr1 functionType <$> sepBy1 applicationTypeExpr (spacedString "->")

typeExpr = functionTypeExpr

-- literalInt = (read :: String -> Integer) <$> withWhitespace (many1 $ satisfy isDigit)

literalDouble = withBreak $ (LiteralExpr . DoubleValue . read) <$> ((string "-" <|> string "") >>++ many (satisfy isDigit) >>++ string "." >>++ many (satisfy isDigit))

-- stringChar = (return <$> satisfy (\x -> x /= '"' && x /= '\\')) <|> (string "\\" >>++ (return <$> satisfy (`elem` "0abfnrtv\"\\")))

-- literalString = (read :: String -> String) <$> (string "\"" >>++ many stringChar >>++ string "\"")

withParens p = spacedString "(" >> p ^>> spacedString ")"

varExpr = VarExpr <$> (lowerId <|> upperId)

atomExpr = literalDouble <|> varExpr <|> withParens expr

applicationExpr = foldl1 AppExpr <$> many1 atomExpr

ofTypeExpr = do
  expr <- applicationExpr
  let rest = do
        spacedString ":"
        t <- typeExpr
        return $ WithTypeExpr expr t
  rest <|> return expr


-- no operators for now


lambdaExpr = do
  spacedString "\\"
  paramNames <- many lowerId
  spacedString "->"
  body <- expr
  return $ foldr LambdaExpr body paramNames

letExpr = do
  stringWithBreak "let"
  var <- lowerId
  -- TODO define functions?
  spacedString "="
  value <- expr
  spacedString ";"
  body <- expr
  return $ AppExpr (LambdaExpr var body) value

defExpr = do
  stringWithBreak "def"
  var <- lowerId
  -- TODO define functions?
  spacedString "="
  value <- expr
  spacedString ";"
  body <- expr
  return $ DefExpr var value body

newTypeExpr = do
  stringWithBreak "newtype"
  typename <- upperId
  params <- many lowerId
  spacedString "="
  t <- typeExpr
  spacedString ";"
  body <- expr
  return $ NewTypeExpr (typename, params, t) body




varPatternExpr = VarPExpr <$> lowerId

constrPatternExpr = do
  constr <- upperId
  return $ ConstrPExpr constr []

atomPatternExpr = varPatternExpr <|> constrPatternExpr <|> withParens patternExpr

appPatternExpr = foldl1 makeApp <$> many1 atomPatternExpr
  where makeApp (ConstrPExpr constr fields) x = ConstrPExpr constr (fields ++ [x])

patternExpr = appPatternExpr

singleCaseExpr = do
  pat <- patternExpr
  spacedString "->"
  body <- expr
  spacedString ";"
  return (pat, body)

caseExpr = do
  stringWithBreak "case"
  value <- expr
  spacedString "{"
  cases <- many singleCaseExpr
  spacedString "}"
  return $ CaseExpr value cases


adtCase = do
  constr <- upperId
  fields <- many typeExpr
  return (constr, fields)

adtExpr = do
  stringWithBreak "data"
  isRec <- (stringWithBreak "rec" >> return True) <|> return False
  typeName <- upperId
  paramNames <- many lowerId
  spacedString "="
  cases <- adtCase `sepBy` spacedString "|"
  spacedString ";"
  body <- expr
  return $ translateNonRecursiveAdtDefinition (typeName, paramNames, cases) body


expr = try letExpr <|> try lambdaExpr <|> try ofTypeExpr

toplevel = spaces >> expr
