{-# LANGUAGE NoMonomorphismRestriction #-}
module Quipp.Parser where

import Control.Applicative ((<$>), (<*>))
import Data.Char
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim


data TypeExpr = ConstructorTypeExpr String | AppTypeExpr TypeExpr TypeExpr | VarTypeExpr String

wordChar = satisfy (\x -> isAlphaNum x || x == '_')

keywords = ["data", "let", "case", "of"]

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

upperId = withWhitespace ((:) <$> satisfy isUpper <*> many wordChar)
lowerId = withWhitespace $ do
  id <- (:) <$> satisfy isUpper <*> many wordChar
  if elem id keywords then fail "Keyword is not an ID" else return id

-- literalInt = (read :: String -> Integer) <$> withWhitespace (many1 $ satisfy isDigit)

literalDouble = (LiteralExpr . DoubleValue . read) <$> (many (satisfy isDigit) >>++ string "." >>++ many (satisfy isDigit))

-- stringChar = (return <$> satisfy (\x -> x /= '"' && x /= '\\')) <|> (string "\\" >>++ (return <$> satisfy (`elem` "0abfnrtv\"\\")))

-- literalString = (read :: String -> String) <$> (string "\"" >>++ many stringChar >>++ string "\"")

withParens p = withWhitespace (string "(") >> p ^>> withWhitespace (string ")")

varExpr = VarExpr <$> lowerId

atomExpr = literalDouble <|> varExpr <|> withParens expr

applicationExpr = foldl1 AppExpr <$> withWhitespace (many atomExpr)


-- no operators for now


lambdaExpr = do
  withWhitespace (string "\\")
  paramNames <- many lowerId
  withWhitespace (string "->")
  body <- expr
  return $ foldr LambdaExpr body paramNames


expr = lambdaExpr <|> applicationExpr

data Declaration = AssignmentDeclaration String Expr

assignmentDeclaration = do
  var <- lowerId
  args <- many lowerId
  withWhitespace (string "=")
  body <- expr
  withWhitespace (string ";")
  return $ AssignmentDeclaration var (foldr LambdaExpr body args)

declaration = assignmentDeclaration

toplevel = many declaration

-- atomType = withParens anyType <|> fmap VarTypeExpr lowerId <|> fmap ConstructorTypeExpr upperId





