{-# LANGUAGE NoMonomorphismRestriction #-}
module Quipp.Parser where

import Control.Applicative ((<$>), (<*>))
import Data.Char
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim

import Quipp.TypeInference
import Quipp.Value


wordChar = satisfy (\x -> isAlphaNum x || x == '_')

keywords = ["data", "let", "in", "case", "of"]

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

upperId = withWhitespace ((:) <$> satisfy isUpper <*> many wordChar)
lowerId = withWhitespace $ do
  id <- (:) <$> satisfy isUpper <*> many wordChar
  if elem id keywords then fail "Keyword is not an ID" else return id

varTypeExpr = VarTExpr <$> lowerId

constTypeExpr = ConstTExpr <$> upperId

atomTypeExpr = varTypeExpr <|> constTypeExpr <|> withParens typeExpr

applicationTypeExpr = foldl1 AppTExpr <$> many1 atomTypeExpr

functionTypeExpr = foldr1 functionType <$> splitBy1 applicationTypeExpr "->"

typeExpr = functionTypeExpr

-- literalInt = (read :: String -> Integer) <$> withWhitespace (many1 $ satisfy isDigit)

literalDouble = (LiteralExpr . DoubleValue . read) <$> (maybe (string "-") >>++ many (satisfy isDigit) >>++ string "." >>++ many (satisfy isDigit))

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
  spacedString "let"
  var <- lowerId
  spacedString "="
  value <- expr
  spacedString ";"
  body <- expr
  return $ LetExpr var value body

adtCase = do
  constr <- upperId
  fields <- many typeExpr
  return (constr, fields)

adtExpr = do
  spacedString "data"
  typeName <- many upperId
  paramNames <- many lowerId
  spacedString "="
  cases <- dataCase `splitBy` spacedString "|"
  spacedString ";"
  body <- expr
  return $ AdtExpr (AdtDefinition typeName paramNames cases) body





expr = letExpr <|> lambdaExpr <|> applicationExpr

-- data Declaration = AssignmentDeclaration String Expr
-- 
-- assignmentDeclaration = do
--   var <- lowerId
--   args <- many lowerId
--   spacedString "="
--   body <- expr
--   spacedString ";"
--   return $ AssignmentDeclaration var (foldr LambdaExpr body args)
-- 
-- declaration = assignmentDeclaration
-- 
-- toplevel = many declaration

-- atomType = withParens anyType <|> fmap VarTypeExpr lowerId <|> fmap ConstructorTypeExpr upperId





