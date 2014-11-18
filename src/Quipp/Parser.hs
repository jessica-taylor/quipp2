{-# LANGUAGE NoMonomorphismRestriction #-}
module Quipp.Parser (toplevel) where

import Debug.Trace
import Control.Applicative ((<$>), (<*>))
import Data.Char
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim

import Quipp.TypeInference
import Quipp.Util
import Quipp.Value

keywords = ["data", "let", "in", "case", "of", "def"]

wordChar = satisfy (\x -> isAlphaNum x || x == '_')

wordBreak = notFollowedBy wordChar

type AdtDefinition = (String, [String], [(String, [TypeExpr])])

varList :: [String]
varList = ["x_" ++ show i | i <- [0..]]

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




-- varPatternExpr = VarPExpr <$> lowerId
-- 
-- constrPatternExpr = do
--   constr <- upperId
--   return $ ConstrPExpr constr []
-- 
-- atomPatternExpr = varPatternExpr <|> constrPatternExpr <|> withParens patternExpr
-- 
-- appPatternExpr = foldl1 makeApp <$> many1 atomPatternExpr
--   where makeApp (ConstrPExpr constr fields) x = ConstrPExpr constr (fields ++ [x])
-- 
-- patternExpr = appPatternExpr
-- 
-- singleCaseExpr = do
--   pat <- patternExpr
--   spacedString "->"
--   body <- expr
--   spacedString ";"
--   return (pat, body)
-- 
-- caseExpr = do
--   stringWithBreak "case"
--   value <- expr
--   spacedString "{"
--   cases <- many singleCaseExpr
--   spacedString "}"
--   return $ CaseExpr value cases


-- adtCase = do
--   constr <- upperId
--   fields <- many typeExpr
--   return (constr, fields)

-- adtExpr = do
--   stringWithBreak "data"
--   typeName <- upperId
--   paramNames <- many lowerId
--   spacedString "="
--   cases <- adtCase `sepBy` spacedString "|"
--   spacedString ";"
--   body <- expr
--   return $ AdtExpr (AdtDefinition typeName paramNames cases) body


expr = try letExpr <|> try lambdaExpr <|> try ofTypeExpr

toplevel = spaces >> expr
