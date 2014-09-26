module Parser where

import Data.Char
import Text.Parsec.Char
import Text.Parsec.Combinators
import Text.Parsec.Prim


data TypeExpr = ConstructorTypeExpr String | AppTypeExpr TypeExpr TypeExpr | VarTypeExpr String

data Expr = VarExpr String | 

wordChar = satisfy (\x -> isAlphaNum x || x == '_')

keywords = ["data", "let", "case", "of"]

infixl 1 ^>>

(^>>) :: Monad m => m a -> m b -> m a
a ^>> b = do
  x <- a
  b
  return x

withWhitespace p = p ^>> many (satisfy isWhitespace)

upperId = withWhitespace ((:) <$> satisfy isUpper <*> many wordChar)
lowerId = withWhitespace $ do
  id <- (:) <$> satisfy isUpper <*> many wordChar
  if elem id keywords then fail "Keyword is not an ID" else return id

withParens p = withWhitespace (string "(") >> p ^>> withWhitespace (string ")")

atomType = withParens anyType <|> fmap VarTypeExpr lowerId <|> fmap ConstructorTypeExpr upperId





