{-# LANGUAGE NoMonomorphismRestriction #-}
module Quipp.Parser (toplevel) where

import Debug.Trace

import Control.Applicative ((<$>), (<*>))
import Control.Monad (mplus)
import Data.Char
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.List (findIndex, inits)
import Data.Maybe (fromJust)
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim

import Quipp.Interpreter
import Quipp.Util
import Quipp.Value

keywords = ["data", "rec", "newtype", "let", "in", "case", "of", "def"]

wordChar = satisfy (\x -> isAlphaNum x || x == '_')

wordBreak = notFollowedBy wordChar

varList :: [String]
varList = ["x_" ++ show i | i <- [0..]]

makeLetExpr :: String -> Expr -> Expr -> Expr
makeLetExpr var value body = AppExpr (LambdaExpr var body) value

type ParseContext = Map String AdtDefinition

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

withParens p = spacedString "(" >> p ^>> spacedString ")"

tupled p unit pair = withParens $ do
  items <- sepBy p (spacedString ",")
  return $ if null items then unit else foldr1 pair items

upperId = withBreak ((:) <$> satisfy isUpper <*> many wordChar)

lowerId = withBreak $ do
  id <- (:) <$> satisfy (\x -> x == '_' || isLower x) <*> many wordChar
  if elem id keywords then fail "Keyword is not an ID" else return id

varTypeExpr = VarTExpr <$> lowerId

constTypeExpr = ConstTExpr <$> upperId

parensTypeExpr = tupled typeExpr (ConstTExpr "Unit") (\x y -> AppTExpr (AppTExpr (ConstTExpr "Pair") x) y)

atomTypeExpr = varTypeExpr <|> constTypeExpr <|> parensTypeExpr

applicationTypeExpr = foldl1 AppTExpr <$> many1 atomTypeExpr

functionTypeExpr = foldr1 functionType <$> sepBy1 applicationTypeExpr (spacedString "->")

typeExpr = functionTypeExpr

-- literalInt = (read :: String -> Integer) <$> withWhitespace (many1 $ satisfy isDigit)

literalDouble = withBreak $ (LiteralExpr . DoubleValue . read) <$> ((string "-" <|> string "") >>++ many (satisfy isDigit) >>++ string "." >>++ many (satisfy isDigit))

literalNat = withBreak $ do
  digits <- many (satisfy isDigit)
  string "N"
  return $ iterate (AppExpr (VarExpr "S")) (VarExpr "Z") !! (read digits :: Int)

-- stringChar = (return <$> satisfy (\x -> x /= '"' && x /= '\\')) <|> (string "\\" >>++ (return <$> satisfy (`elem` "0abfnrtv\"\\")))

-- literalString = (read :: String -> String) <$> (string "\"" >>++ many stringChar >>++ string "\"")


varExpr = VarExpr <$> (lowerId <|> upperId)

parensExpr ctx = tupled (expr ctx) (VarExpr "Unit") (\x y -> AppExpr (AppExpr (VarExpr "Pair") x) y)

atomExpr ctx = try literalDouble <|> literalNat <|> varExpr <|> parensExpr ctx

applicationExpr ctx = foldl1 AppExpr <$> many1 (atomExpr ctx)

ofTypeExpr ctx = do
  expr <- applicationExpr ctx
  let rest = do
        spacedString ":"
        t <- typeExpr
        return $ WithTypeExpr expr t
  rest <|> return expr


-- no operators for now

definition ctx = do
  var <- lowerId
  args <- many lowerId
  spacedString "="
  value <- expr ctx
  spacedString ";"
  return (var, foldr LambdaExpr value args)

lambdaExpr ctx = do
  spacedString "\\"
  paramNames <- many lowerId
  spacedString "->"
  body <- expr ctx
  return $ foldr LambdaExpr body paramNames

letExpr ctx = do
  stringWithBreak "let"
  (var, value) <- definition ctx
  body <- expr ctx
  return $ makeLetExpr var value body

defExpr ctx = do
  stringWithBreak "def"
  varvalues <- definition ctx `sepBy1` spacedString ","
  body <- expr ctx
  return $ DefExpr varvalues body


varPatternExpr = VarPExpr <$> lowerId

constrPatternExpr = do
  constr <- upperId
  return $ ConstrPExpr constr []

parensPatternExpr = tupled patternExpr (ConstrPExpr "Unit" []) (\x y -> ConstrPExpr "Pair" [x, y])

atomPatternExpr = varPatternExpr <|> constrPatternExpr <|> parensPatternExpr

makeAppPattern (ConstrPExpr constr fields) x = ConstrPExpr constr (fields ++ [x])

appPatternExpr = foldl1 makeAppPattern <$> many1 atomPatternExpr

patternExpr = appPatternExpr

singleCaseExpr ctx = do
  pat <- patternExpr
  spacedString "->"
  body <- expr ctx
  spacedString ";"
  return (pat, body)

caseExpr ctx = do
  stringWithBreak "case"
  value <- expr ctx
  spacedString "{"
  cases <- many (singleCaseExpr ctx)
  spacedString "}"
  return $ CaseExpr value cases


adtCase = do
  constr <- upperId
  fields <- many atomTypeExpr
  return (constr, fields)

adtExpr ctx = do
  stringWithBreak "data"
  typeName <- upperId
  paramNames <- many lowerId
  spacedString "="
  cases <- adtCase `sepBy` spacedString "|"
  spacedString ";"
  let def = (typeName, paramNames, cases)
  body <- expr (foldr (uncurry Map.insert) ctx [(c, def) | (c, _) <- cases])
  return $ AdtDefExpr def body

expr ctx = try (letExpr ctx) <|> try (defExpr ctx) <|> try (lambdaExpr ctx) <|> try (ofTypeExpr ctx)
           <|> try (adtExpr ctx) <|> try (caseExpr ctx)
           -- <|> try (newTypeExpr ctx) 

toplevel = spaces >> expr Map.empty
