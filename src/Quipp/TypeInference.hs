





data AnnotatedExpr = VarAExpr String | LambdaAExpr [(String, AnnotatedExpr)] String AnnotatedExpr AnnotatedExpr | AppAExpr AnnotatedExpr [AnnotatedExpr] AnnotatedExpr

data Expr = VarExpr String | LambdaExpr [(String, Expr)] String (Maybe Expr) Expr | AppExpr Expr (Maybe [Expr]) Expr



insertAll :: Ord k => [(k, v)] -> Map k v -> Map k v
insertAll = foldr (uncurry Map.insert)

setInsertAll :: Ord k => [k] -> Set k -> Set k
setInsertAll = foldr Set.insert

mapmExpr' :: Monad m => Set String -> (String -> m Expr) -> Expr -> m Expr

mapmExpr' exclude f e@(VarExpr s) | Set.member s exclude = e
                                  | otherwise = f s

mapmExpr' exclude f (AppExpr fun gens arg) = do
  fun' <- mapmExpr' exclude f fun
  gens' <- fmapM (fmapM (mapmExpr' exclude f)) gens
  arg' <- mapmExpr' exclude f arg
  return AppExpr fun' gens' arg'

mapmExpr' exclude f (LambdaExpr gen param paramType body) = do
  gen' <- forM gen $ \(g, t) -> liftM (g,) $ mapmExpr' exclude f t
  let exclude' = setInsertAll (map fst gen) exclude
  paramType' <- fmapM (mapmExpr' exclude' f) paramType
  let exclude'' = Set.insert param exclude'
  body' <- mapmExpr' exclude'' f body
  return (LambdaExpr gen' param paramType' body')

mapmExpr = mapmExpr' Set.empty

substExpr :: Map String Expr -> Expr -> Expr
substExpr subst = runIdentity . mapmExpr (return . substitute)
  where substitute v = case Map.lookup v subst of
          Nothing -> VarExpr v
          Just x -> x

synthesizeExpr :: Map String AnnotatedExpr -> Expr -> Either String AnnotatedExpr

synthesizeExpr ctx (VarExpr v)
  | Map.member v ctx = return (VarAExpr v)
  | otherwise = Left ("Unknown variable " ++ v)

synthesizeExpr ctx (LambdaExpr _ _ Nothing _) = Left "Cannot synthesize unannotated lambda"

synthesizeExpr ctx (LambdaExpr gen param (Just paramType) body) = do
  -- TODO sequence?
  annGen <- mapM (\(gvar, gtype) -> liftM (gvar,) (synthesizeExpr ctx gtype)) gen
  let ctx' = insertAll annGen ctx
  annParamType <- synthesizeExpr ctx' paramType
  let ctx'' = Map.insert param annParamType ctx'
  annBody <- synthesizeExpr ctx'' body
  return $ LambdaAExpr annGen param annParamType annBody

synthesizeExpr ctx (AppExpr fun Nothing arg) = do
  annFun <- synthesizeExpr ctx fun
  annArg <- synthesizeExpr ctx arg
  -- TODO substitute

synthesizeExpr ctx (AppExpr fun (Just gen) arg) = do
  annFun <- synthesizeExpr ctx fun
  annGen <- mapM (synthesizeExpr ctx) gen
  -- TODO ctx


  
  

