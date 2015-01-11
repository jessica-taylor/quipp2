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

import Quipp.TypeInference
import Quipp.Util
import Quipp.Value

keywords = ["data", "rec", "newtype", "let", "in", "case", "of", "def"]

wordChar = satisfy (\x -> isAlphaNum x || x == '_')

wordBreak = notFollowedBy wordChar

type AdtDefinition = (String, [String], [(String, [TypeExpr])])

varList :: [String]
varList = ["x_" ++ show i | i <- [0..]]

makeLetExpr :: String -> Expr -> Expr -> Expr
makeLetExpr var value body = AppExpr (LambdaExpr var body) value

type ParseContext = Map String AdtDefinition

translateNonRecursiveAdtDefinition :: AdtDefinition -> Expr -> Expr
translateNonRecursiveAdtDefinition (name, params, cases) body =
  let pairExpr x y = AppExpr (AppExpr (VarExpr "_pair") x) y
      leftExpr = AppExpr (VarExpr "_left")
      rightExpr = AppExpr (VarExpr "_right")
      nestedTuple unit pair lst = if null lst then unit else foldr1 pair lst
      getConstr i ts = foldr LambdaExpr (AppExpr (VarExpr ("Make" ++ name)) $ rightsAndLeft $ nestedTuple (VarExpr "_unit") pairExpr (map VarExpr vars)) vars
        where vars = take (length ts) varList
              rightsAndLeft | i == length cases - 1 = funPow i rightExpr
                            | otherwise = leftExpr . funPow i rightExpr
  in NewTypeExpr (name, params, foldr1 eitherType [nestedTuple (ConstTExpr "_Unit") pairType ts | (_, ts) <- cases])
      $ foldr (\(i, (constrName, ts)) -> makeLetExpr constrName (getConstr i ts)) body (zip [0..] cases)

translateRecursiveAdtDefinition :: AdtDefinition -> Expr -> Expr
translateRecursiveAdtDefinition (name, params, cases) body =
  let recVar = name ++ "_rec"
      fixCase (caseName, ts) = (caseName ++ "F", map fixType ts)
      recType = foldl AppTExpr (ConstTExpr name) $ map VarTExpr (name:params)
      fixType t | t == recType = VarTExpr recVar
      fixType (AppTExpr fun arg) = AppTExpr (fixType fun) (fixType arg)
      fixType (ConstTExpr t) | t == name = error $ "Cannot handle polymorphic recursion in type " ++ name
      fixType other = other
      getConstr (caseName, ts) = foldr LambdaExpr (AppExpr (VarExpr "mu") $ foldl1 AppExpr $ map VarExpr ((caseName ++ "F"):vars)) vars
        where vars = take (length ts) varList
  in translateNonRecursiveAdtDefinition (name ++ "F", params ++ [recVar], map fixCase cases) $
       NewTypeExpr (name, params, AppTExpr (ConstTExpr "Mu") (foldl AppTExpr (ConstTExpr (name ++ "F")) $ map VarTExpr params)) $
         foldr (\cas b -> makeLetExpr (fst cas) (getConstr cas) b) body cases


data PatternExpr = VarPExpr String | ConstrPExpr String [PatternExpr] deriving (Eq, Ord, Show)

data PrimPatternExpr = VarPPExpr String | UnitPPExpr | PairPPExpr PrimPatternExpr PrimPatternExpr | LeftPPExpr PrimPatternExpr | RightPPExpr PrimPatternExpr | NewtypeConstrPPExpr String PrimPatternExpr deriving Show

toPrimPat :: (String -> AdtDefinition) -> PatternExpr -> PrimPatternExpr
toPrimPat _ (VarPExpr s) = VarPPExpr s
toPrimPat constrDef (ConstrPExpr constr fields) =
  let (adtName, _, adtCases) = constrDef constr
      caseIndex = fromJust $ findIndex ((== constr) . fst) adtCases
      leftsAndRight | caseIndex == length adtCases - 1 = funPow caseIndex RightPPExpr
                    | otherwise = LeftPPExpr . funPow caseIndex RightPPExpr
  in NewtypeConstrPPExpr ("Make" ++ adtName) $ leftsAndRight $ foldr PairPPExpr UnitPPExpr $ map (toPrimPat constrDef) fields

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
lensToExpr lens val = foldr (\l -> AppExpr (VarExpr (if l then "_snd" else "_fst"))) val lens

modifyLensExpr :: PrimPatternLens -> Expr -> Expr -> Expr
modifyLensExpr [] f x = AppExpr f x
modifyLensExpr (False:ls) f x =
  foldl1 AppExpr [VarExpr "_pair", modifyLensExpr ls f (AppExpr (VarExpr "_fst") x), AppExpr (VarExpr "_snd") x]
modifyLensExpr (True:ls) f x =
  foldl1 AppExpr [VarExpr "_pair", AppExpr (VarExpr "_fst") x, modifyLensExpr ls f (AppExpr (VarExpr "_snd") x)]

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

pointToAnyExpandable :: [PrimPatternExpr] -> Maybe (PrimPatternLens, Maybe String)
pointToAnyExpandable = foldl1 mplus . map pointToExpandable

partitionCase :: PrimPatternLens -> (PrimPatternExpr, Expr) -> ([(PrimPatternExpr, Expr)], [(PrimPatternExpr, Expr)])
partitionCase lens x | trace ("\nPC: " ++ show lens ++ " " ++ show x) False = undefined
partitionCase lens (VarPPExpr v, body) =
  let part f = [(VarPPExpr v, AppExpr (LambdaExpr v body) $ modifyLensExpr lens (VarExpr f) (VarExpr v))]
  in (part "_left", part "_right")
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
  (VarPPExpr v, AppExpr (LambdaExpr v body) $ modifyLensExpr lens (VarExpr ("Make" ++ constrName)) (VarExpr v))
expandNewtypeCase [] constrName (NewtypeConstrPPExpr constrName' p, body)
  | constrName == constrName' = (p, body)
expandNewtypeCase (False:l) constrName (PairPPExpr f s, body) =
  let (f', b) = expandNewtypeCase l constrName (f, body) in (PairPPExpr f' s, b)
expandNewtypeCase (True:l) constrName (PairPPExpr f s, body) =
  let (s', b) = expandNewtypeCase l constrName (s, body) in (PairPPExpr f s', b)

fullyExpandedMatch :: Expr -> (PrimPatternExpr, Expr) -> Expr
fullyExpandedMatch ex (VarPPExpr v, body) = AppExpr (LambdaExpr v body) ex
fullyExpandedMatch ex (PairPPExpr f s, body) =
  fullyExpandedMatch (AppExpr (VarExpr "_fst") ex)
    (f, fullyExpandedMatch (AppExpr (VarExpr "_snd") ex) (s, body))
fullyExpandedMatch ex (UnitPPExpr, body) = body
fullyExpandedMatch ex (other, body) =
  error $ "Cannot fully expand match " ++ show ex ++ " with " ++ show (other, body)

casesToExpr :: Int -> Expr -> [(PrimPatternExpr, Expr)] -> Expr
casesToExpr depth ex cases =
  let cases' = removeRedundantCases cases
      varname = "__cases_to_expr_" ++ show depth in
  case pointToAnyExpandable (map fst cases') of
    Nothing -> fullyExpandedMatch ex (head cases')
    Just (lens, Nothing) ->
      let (leftCases, rightCases) = partitionCases lens cases'
          handler cs = LambdaExpr varname $ casesToExpr (depth + 1) (modifyLensExpr lens (LambdaExpr "__ignored" (VarExpr varname)) ex) cs
      in trace ("\nLRC: " ++ show (leftCases, rightCases)) $ foldl1 AppExpr [VarExpr "_either", lensToExpr lens ex, handler leftCases, handler rightCases]
    Just (lens, Just ntname) | take 4 ntname == "Make" ->
      let newCases = map (expandNewtypeCase lens ntname) cases'
      in casesToExpr (depth + 1) (modifyLensExpr lens (VarExpr ("un" ++ drop 4 ntname)) ex) newCases
    Just (lens, Just ntname) -> error ("casesToExpr failed: cases = " ++ show cases ++ ", lens = " ++ show lens ++ ", ntname = " ++ ntname)

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

newTypeExpr ctx = do
  stringWithBreak "newtype"
  typename <- upperId
  params <- many lowerId
  spacedString "="
  t <- typeExpr
  spacedString ";"
  body <- expr ctx
  return $ NewTypeExpr (typename, params, t) body


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
  return (toPrimPat (ctx !) pat, body)

caseExpr ctx = do
  stringWithBreak "case"
  value <- expr ctx
  spacedString "{"
  cases <- many (singleCaseExpr ctx)
  spacedString "}"
  return $ casesToExpr 0 value cases


adtCase = do
  constr <- upperId
  fields <- many atomTypeExpr
  return (constr, fields)

adtExpr ctx = do
  stringWithBreak "data"
  isRec <- (stringWithBreak "rec" >> return True) <|> return False
  typeName <- upperId
  paramNames <- many lowerId
  spacedString "="
  cases <- adtCase `sepBy` spacedString "|"
  spacedString ";"
  let def = (typeName, paramNames, cases)
  trace ("DATA: " ++ show def) $ return ()
  body <- expr (foldr (uncurry Map.insert) ctx [(c, def) | (c, _) <- cases])
  return $ (if isRec then translateRecursiveAdtDefinition else translateNonRecursiveAdtDefinition) def body


expr ctx = try (letExpr ctx) <|> try (defExpr ctx) <|> try (lambdaExpr ctx) <|> try (ofTypeExpr ctx)
           <|> try (adtExpr ctx) <|> try (caseExpr ctx)
           -- <|> try (newTypeExpr ctx) 

toplevel = spaces >> expr Map.empty
