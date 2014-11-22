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
      getConstr i ts = foldr LambdaExpr (leftsAndRight $ foldr pairExpr (VarExpr "unit") (map VarExpr vars)) vars
        where vars = take (length ts) varList
              leftsAndRight | i == length cases - 1 = funPow i rightExpr
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

data PrimPatternExpr = VarPPExpr String | UnitPPExpr | PairPPExpr PrimPatternExpr PrimPatternExpr | LeftPPExpr PrimPatternExpr | RightPPExpr PrimPatternExpr

patsByEither pats =
  ([(l ++ rest, body) | (LeftPPExpr l:rest, body) <- pats] ++
   [(VarPPExpr v:rest, AppExpr (LambdaExpr v body) (AppExpr (VarExpr "left") v)) | (VarPPExpr v:rest, body) <- pats]),

   [(r ++ rest, body) | (RightPPExpr r:rest, body) <- pats] ++
   [(VarPPExpr v:rest, AppExpr (LambdaExpr v body) (AppExpr (VarExpr "right") v)) | (VarPPExpr v:rest, body) <- pats])


-- Key question: "do I need to do something differently depending on if the
-- first thing is a Left or a Right?"
casesToExpr :: Expr -> [(PrimPatternExpr, Expr)] -> Expr
casesToExpr ex cases =
  let cases' = removeRedundantCases cases
      (leftCases, rightCases) = patsByEither cases'
  in if length leftCases == 0 || length rightCases == 0 then undefined
     else if leftCases == rightCases then
            let VarPPExpr varname = head $ fst $ head leftCases
            in AppExpr (LambdaExpr varname (casesToExpr xs (map restCases (tail cases')))) x
     else let varname = "__casesToExpr_" ++ length cases in
          foldl1 AppExpr [VarExpr "either", x, LambdaExpr varname $ casesToExpr (VarExpr varname : xs) leftCases, LambdaExpr varname $ casesToExpr (VarExpr varname : ys) rightCases]





-- How to convert pattern matching to uses of 'either' function?
-- In the general case, we are pattern matching on a tuple.
-- Idea: figure out what queries we need to make.
-- Query the first; then if we haven't reduced it enough, query the second, etc

patsMatchingConstructor :: Int -> String -> [([PatternExpr], Expr)] -> ([([PatternExpr], Expr)], [([PatternExpr], Expr)])
patsMatchingConstructor i constr = partition (matchesConstr . (!! i) . fst)
  where matchesConstr (VarPExpr _) = True
        matchesConstr (ConstrPExpr c _) = c == constr

patsImply :: [PatternExpr] -> [PatternExpr] -> Bool
patsImply pats1 pats2
  | length pats1 != length pats2 = undefined
  | otherwise = all (zipWith patImplies pats1 pats2)

patImplies _ (VarPExpr _) = True
patImplies (VarPExpr _) (ConstrPExpr _ _) = False
patImplies (ConstrPExpr c1 f1) (ConstrPExpr c2 f2) =
  c1 == c2 && patsImply f1 f2

removeRedundantPats :: [[PatternExpr]] -> [[PatternExpr]]
removeRedundantPats pats = foldl (\pat rest -> if any (flip patsImply pat) rest then rest else pat:rest) [] pats

relevantConstrs :: [[PatternExpr]] -> [(Int, String)]
relevantConstrs ps = [(i, constr) | p <- ps, (i, ConstrPExpr constr _) <- zip [0..] p]

data CaseTree = SingleCase Expr | CaseTest Int [(String, [([PatternExpr], Expr

filterVarPats :: [(PatternExpr, Expr)] -> ([(String, [PatternExpr], Expr)], Maybe (String, Expr))
filterVarPats pats =
  case [(i, var, body) | (i, (VarExpr var, body)) <- zip [0..] pats] of
    Nothing -> (fromConstrs pats, Nothing)
    Just (i, var, varbody) -> (fromConstrs (take i pats), Just (var, varbody))
  where fromConstrs xs = [(constr, fields, body) | (ConstrPExpr constr fields, body) <- xs]


groupByToplevelConstrs :: [(PatternExpr, Expr)] -> ([(String, [([PatternExpr], Expr)])], Maybe (PatternExpr, Expr))
groupByToplevelConstrs pats =
  let (constrPats, varPat) = filterVarPats pats
      groupedConstrs = groupAnywhereBy fst3 constrPats
  in ([(fst3 (head g), zip (map snd3 g) (map thd3 g)) | g <- groupedConstrs],
      varPat)

caseToEither :: Expr -> [(PatternExpr, Expr)] -> Expr
caseToEither x cases


caseMultiToEither :: [Expr] -> [([PatternExpr], Expr)] -> Expr
caseMultiToEither xs cases =

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
