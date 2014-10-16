{-# LANGUAGE NoMonomorphismRestriction #-}
module Quipp.Parser (toplevel) where

import Debug.Trace
import Control.Applicative ((<$>), (<*>))
import Data.Char
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim

import Quipp.TypeInference
import Quipp.Value

keywords = ["data", "let", "in", "case", "of"]

wordChar = satisfy (\x -> isAlphaNum x || x == '_')

wordBreak = notFollowedBy wordChar

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
  return $ LetExpr var value body

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
  typeName <- upperId
  paramNames <- many lowerId
  spacedString "="
  cases <- adtCase `sepBy` spacedString "|"
  spacedString ";"
  body <- expr
  return $ AdtExpr (AdtDefinition typeName paramNames cases) body


expr = try letExpr <|> try lambdaExpr <|> try applicationExpr <|> try adtExpr <|> try caseExpr

toplevel = spaces >> expr
