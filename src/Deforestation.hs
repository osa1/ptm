{-# LANGUAGE GeneralizedNewtypeDeriving, LambdaCase, OverloadedStrings,
             TupleSections #-}

module Deforestation where

import Control.Monad.State.Strict
import Data.Bifunctor (second)
import Data.List (deleteBy, foldl', sortBy, (\\))
import qualified Data.Map as M
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Set as S
import Data.String (IsString (..))
import qualified Language.Haskell.Exts as HSE

-- import qualified Debug.Trace

trace :: String -> a -> a
trace _ = id

type Var = String
type Constr = String

data Term
  = Var Var
  | Constr Constr [Term]
  | App Var [Term]
  | Case Term [(Pat, Term)]
  deriving (Show)

instance IsString Term where
    fromString = Var

data Pat = Pat Constr [Var]
  deriving (Show)

data Fn = Fn [Var] Term deriving (Show)

data TTerm
  = TVar Var
  | TConstr Constr [TTerm]
  | TApp Var [Var]
  | TCase Var [(Pat, TTerm)]
  deriving (Show)

type Env = M.Map Var Fn

lookupFn :: Env -> Var -> Fn
lookupFn e v = case M.lookup v e of
                 Nothing ->
                   error $ "Can't find function " ++ v ++ " in env: " ++ show (M.keysSet e)
                 Just f -> f

data Hist
  = FunCall Var [Term]
  | Match Term [(Pat, Term)]
  deriving (Show)

type History = [(Hist, Var {- function name -})]

-- we only keep track of applications
data DState = DState
  { history :: History
  , defs    :: [(Var, [Var], TTerm)]
  }

deforest :: Env -> Term -> State DState TTerm
-- rule 1
deforest _   (Var v) = trace "rule 1" $ return $ TVar v
-- rule 2
deforest env (Constr c ts) = trace "rule 2" $ TConstr c <$> mapM (deforest env) ts
-- rule 3
deforest env t@(App v ts) = trace "rule 3" $ do
    hist <- gets history
    case checkAppRenaming (v, ts) hist of
      Just tt -> return tt
      Nothing -> do
        let Fn args body = lookupFn env v
        if length args /= length ts
          then error "Function arity doesn't match with # applied arguments"
          else do
            let hName = 'h' : show (length hist)
            modify $ \s -> s{history = ((FunCall v ts, hName) : hist)}
            -- Linearity means that each argument is used once in the body. This
            -- is how we guarantee that there won't be work duplication.
            -- TODO: We don't check for it though. How to guarantee that there
            -- won't be work duplication?

            -- Careful with capturing here. Example case to be careful:
            --   (\x y -> ...) (... y ...) (...)
            let fvs = fvsTerm t `S.difference` M.keysSet env
                args' = take (length args) (freshIn fvs)
            ret <- deforest env $ substTerms args' ts (substTerms args (map Var args') body)
            modify $ \s -> s{defs = (hName, S.toList fvs, ret) : defs s}
            return $ TApp hName (S.toList fvs)
-- rule 4
deforest env t@(Case (Var v) cases) = trace "rule 4" $ do
    hist <- gets history
    case checkCaseRenaming (Var v, cases) hist of
      Just tt -> return tt
      Nothing -> do
        let hName = 'h' : show (length hist)
        modify $ \s -> s{history = ((Match (Var v) cases, hName) : hist)}
        let fvs = fvsTerm t `S.difference` M.keysSet env
        ret <- TCase v <$> mapM (\(p, r) -> (p,) <$> deforest env r) cases
        modify $ \s -> s{defs = (hName, S.toList fvs, ret) : defs s}
        return $ TApp hName (S.toList fvs)
-- rule 5
deforest env (Case (Constr c ts) cases) = trace "rule 5" $
    let (vs, rhs) = findCase cases
     in deforest env $ substTerms vs ts rhs
  where
    findCase [] = error $ "Can't find matching case for " ++ show c
    findCase ((Pat con vs, rhs) : cs)
      | c == con  = (vs, rhs)
      | otherwise = findCase cs
-- rule 6
deforest env t@(Case (App f ts) cases) = trace "rule 6" $ do
    let Fn args body = lookupFn env f
    let fvs = fvsTerm t `S.difference` M.keysSet env
        args' = take (length args) (freshIn  fvs)
    deforest env $
      Case (substTerms args' ts (substTerms args (map Var args') body)) cases
    -- hist <- gets history
    -- case checkCaseRenaming (App f ts, cases) hist of
    --   Just tt -> return tt
    --   Nothing -> do
    --     let hName = 'h' : show (length hist)
    --     modify $ \s -> s{history = ((Match (App f ts) cases, hName) : hist)}
    --     let Fn args body = lookupFn env f
    --     if length args /= length ts
    --       then error "Function arity doesn't match with # applied arguments"
    --       else do
    --         -- see comments in rule (3)
    --         let fvs = fvsTerm t `S.difference` M.keysSet env
    --             args' = take (length args) (freshIn  fvs)
    --         ret <- deforest env $
    --                  Case (substTerms args' ts (substTerms args (map Var args') body)) cases
    --         modify $ \s -> s{defs = (hName, S.toList fvs, ret) : defs s}
    --         return $ TApp hName (S.toList fvs)
-- rule 7
deforest env tm@(Case (Case t cases) cases') = trace "rule 7" $
    -- we should rename pattern variables in inner case to avoid capturing
    -- variables in outer case's RHSs (see also comments in CoreLike.Simplify
    -- for an example case)
    deforest env $ Case t $ flip map cases $ \(p@(Pat _ vs), rhs) ->
      -- use vsTerm instead of fvsTerm for clarity
      let renamings  = zip vs $ freshIn (vsTerm tm)
          (p', rhs') = renamePat renamings (p, rhs)
       in (p', Case rhs' cases')

isRenaming :: Term -> Term -> Maybe [(Var, Var)]
isRenaming (Var v1) (Var v2) = Just [(v1, v2)]
isRenaming (Constr c1 ts1) (Constr c2 ts2) = do
    guard $ c1 == c2
    guard $ length ts1 == length ts2
    mapM (uncurry isRenaming) (zip ts1 ts2) >>= tryJoinRs . concat
isRenaming (App fs1 ts1) (App fs2 ts2) = do
    guard $ fs1 == fs2
    guard $ length ts1 == length ts2
    mapM (uncurry isRenaming) (zip ts1 ts2) >>= tryJoinRs . concat

isRenaming (Case t1 cases1) (Case t2 cases2) = do
    guard $ length cases1 == length cases2
    rs1 <- isRenaming t1 t2
    -- TODO: Should I sort cases by constructor name before this?
    casesRs <- forM (zip cases1 cases2) $ \((Pat c1 vs1, rhs1), (Pat c2 vs2, rhs2)) -> do
      guard $ c1 == c2
      let binderRs = zip vs1 vs2
      rhsRs <- isRenaming rhs1 rhs2
      -- binders should be renamed according to `binderRs`, otherwise we fail
      (\\ binderRs) <$> tryJoinRs rhsRs >>= tryJoinBinderRs binderRs
    tryJoinRs $ rs1 ++ concat casesRs
  where
    tryJoinBinderRs :: [(Var, Var)] -> [(Var, Var)] -> Maybe [(Var, Var)]
    tryJoinBinderRs _ [] = Just []
    tryJoinBinderRs binderRs ((v1, v2) : rest) =
      case lookup v1 binderRs of
        Nothing -> ((v1, v2) :) <$> tryJoinBinderRs binderRs rest
        Just v2'
          | v2 == v2' -> tryJoinBinderRs binderRs rest
          | otherwise -> Nothing

isRenaming _ _ = Nothing

tryJoinRs :: [(Var, Var)] -> Maybe [(Var, Var)]
tryJoinRs [] = Just []
tryJoinRs ((r, l) : rest) =
    case lookup r rest of
      Nothing -> ((r, l) :) <$> tryJoinRs rest
      Just l'
        | l == l'   ->
            tryJoinRs ((r, l) : deleteBy (\(r1, _) (r2, _) -> r1 == r2) (r, l) rest)
        | otherwise -> Nothing

checkAppRenaming :: (Var, [Term]) -> History -> Maybe TTerm
checkAppRenaming (fName, args) h0 = iter [ (v, ts, h) | (FunCall v ts, h) <- h0 ]
  where
    iter [] = Nothing
    iter ((f, as, h) : rest) =
      case isRenaming (App f as) (App fName args) of
        Just substs -> Just $ TApp h (map snd $ sortBy (\(v1, _) (v2, _) -> v1 `compare` v2) substs)
        Nothing     -> iter rest

checkCaseRenaming :: (Term, [(Pat, Term)]) -> History -> Maybe TTerm
checkCaseRenaming (scrt, cases) h0 = iter [ (t, cs, h) | (Match t cs, h) <- h0 ]
  where
    iter [] = Nothing
    iter ((scrt', cases', h) : rest) =
      case isRenaming (Case scrt' cases') (Case scrt cases) of
        Just substs ->
            Just $ TApp h (map snd $ sortBy (\(v1, _) (v2, _) -> v1 `compare` v2) substs)
        Nothing     -> iter rest

------------------
-- * Substitutions

substTerms :: [Var] -> [Term] -> Term -> Term
substTerms vs ts t0 = foldl' (\t (v, s) -> substTerm v s t) t0 (zip vs ts)

substTerm :: Var -> Term -> Term -> Term
substTerm v t t0@(Var v')
  | v == v'   = t
  | otherwise = t0
substTerm v t (Constr c ts) = Constr c (map (substTerm v t) ts)
substTerm v t (App f body) = App f (map (substTerm v t) body)
substTerm v t (Case scrt cases) = Case (substTerm v t scrt) (map substCase cases)
  where
    substCase :: (Pat, Term) -> (Pat, Term)
    substCase p@(Pat _ vs, rhs)
      | v `elem` vs = p
      | otherwise =
          let captures = S.toList $ S.fromList vs `S.intersection` fvsTerm t
              renamings = zip captures $ freshIn $
                S.insert v $ fvsTerm rhs `S.union` S.fromList vs `S.union` fvsTerm t
           in second (substTerm v t) $ renamePat renamings p

renamePat :: [(Var, Var)] -> (Pat, Term) -> (Pat, Term)
renamePat rs (Pat c vs, rhs) =
  ( Pat c (map (\v' -> fromMaybe v' (lookup v' rs)) vs)
  , uncurry substTerms (unzip (map (second Var) rs)) rhs )

--------------------------------------------------------------------
-- * Free and bound variables in terms and fresh variable generation

-- | Free variables in given term.
fvsTerm :: Term -> S.Set Var
fvsTerm (Var v) = S.singleton v
fvsTerm (Constr _ ts) = S.unions $ map fvsTerm ts
fvsTerm (App v ts) = S.insert v $ S.unions $ map fvsTerm ts
fvsTerm (Case t cases) = S.unions $ fvsTerm t : map fvsCase cases

fvsCase :: (Pat, Term) -> S.Set Var
fvsCase (Pat _ vs, rhs) = fvsTerm rhs `S.difference` S.fromList vs

-- | All variables used in given term.
vsTerm :: Term -> S.Set Var
vsTerm (Var v) = S.singleton v
vsTerm (Constr _ ts) = S.unions $ map vsTerm ts
vsTerm (App v ts) = S.insert v $ S.unions $ map vsTerm ts
vsTerm (Case t cases) = S.unions $ vsTerm t : map vsCase cases

vsCase :: (Pat, Term) -> S.Set Var
vsCase (Pat _ vs, rhs) = vsTerm rhs `S.union` S.fromList vs

freshIn :: S.Set Var -> [Var]
freshIn vs = filter (not . flip S.member vs) $ map (("v_" ++) . show) [0 :: Int ..]

fvsTT :: TTerm -> S.Set Var
fvsTT (TVar v) = S.singleton v
fvsTT (TConstr _ ts) = S.unions $ map fvsTT ts
fvsTT (TApp f vs) = S.fromList $ f : vs
fvsTT (TCase v cases) = S.insert v $ S.unions $ map fvsTCase cases
  where
    fvsTCase :: (Pat, TTerm) -> S.Set Var
    fvsTCase (Pat _ vs, rhs) = fvsTT rhs `S.difference` (S.fromList vs)

------------------------------------------------
-- * Example functions, programs and environment

append_fn :: Fn
append_fn =
  Fn ["xs", "ys"] $ Case (Var "xs")
    [ (Pat "Nil" [], Var "ys")
    , (Pat "Cons" ["x", "xs"], Constr "Cons" [Var "x", App "append" [Var "xs", Var "ys"]])
    ]

flip_fn :: Fn
flip_fn =
  Fn ["zt"] $ Case (Var "zt")
    [ (Pat "Leaf" ["z"], Constr "Leaf" [Var "z"])
    , (Pat "Branch" ["xt", "yt"], Constr "Branch" [App "flip" [Var "yt"],
                                                   App "flip" [Var "xt"]])
    ]

testEnv :: Env
testEnv = M.fromList
  [ ("flip", flip_fn)
  , ("append", append_fn)
  ]

append_pgm :: Term
append_pgm = App "append" [App "append" [Var "xs", Var "ys"], Var "zs"]

flip_pgm :: Term
flip_pgm = App "flip" [App "flip" [Var "zt"]]

deforest' :: Term -> ([(Var, [Var], TTerm)], TTerm)
deforest' t =
    let (tt, DState _ ds) = runState (deforest testEnv t) (DState [] [])
     in (ds, tt)

-------------------------
-- * Parsing and printing

-- (mostly copied from CoreLike.Parser)

parseTerm :: String -> Either String Term
parseTerm contents =
    case HSE.parseExp contents of
      HSE.ParseOk hse -> transformHSE hse
      HSE.ParseFailed loc str ->
        Left $ "fromParseResult: Parse failed at [" ++ HSE.srcFilename loc
                 ++ "] (" ++ show (HSE.srcLine loc) ++ ":"
                 ++ show (HSE.srcColumn loc) ++ "): " ++ str

transformHSE :: HSE.Exp -> Either String Term
transformHSE (HSE.Var qname) = Var <$> transformQName qname
transformHSE (HSE.App e1 e2) = do
    e2' <- transformHSE e2
    transformHSE e1 >>= \case
      App v ts    -> return $ App v (ts ++ [e2'])
      Constr c ts -> return $ Constr c (ts ++ [e2'])
      Var v       -> return $ App v [e2']
      e           -> Left $ "Unsupported function in application syntax: " ++ show e
transformHSE (HSE.Case e alts) = Case <$> transformHSE e <*> mapM transformAlt alts
transformHSE (HSE.Paren e) = transformHSE e
transformHSE (HSE.Con qname) = flip Constr [] <$> transformQName qname
transformHSE e = Left $ "Unsupported HSE expression: " ++ show e

transformAlt :: HSE.Alt -> Either String (Pat, Term)
transformAlt (HSE.Alt _ pat rhs _) = (,) <$> transformPat pat <*> transformRhs rhs

transformPat :: HSE.Pat -> Either String Pat
transformPat (HSE.PApp qname pats) = Pat <$> transformQName qname <*> mapM collectArg pats
transformPat p = Left $ "transformPat: Unsupported pattern: " ++ show p

collectArg :: HSE.Pat -> Either String Var
collectArg (HSE.PVar v) = return $ nameVar v
collectArg p =
    Left $ "collectArgs: Unsupported pattern in function arguments: " ++ show p

transformRhs :: HSE.Rhs -> Either String Term
transformRhs (HSE.GuardedRhss rhss) = Left $ "Guarded RHSs are not supported: " ++ show rhss
transformRhs (HSE.UnGuardedRhs e) = transformHSE e

transformQName :: HSE.QName -> Either String Var
transformQName q@HSE.Qual{} = Left $ "Qualified names are not supported: " ++ show q
transformQName (HSE.UnQual n) = return $ nameVar n
transformQName (HSE.Special HSE.Cons) = return "(:)"
transformQName (HSE.Special HSE.UnitCon) = return "()"
transformQName (HSE.Special s) = Left $ "Unsupported special name: " ++ show s

nameVar :: HSE.Name -> Var
nameVar (HSE.Ident s)  = s
nameVar (HSE.Symbol s) = s

toHSE :: TTerm -> HSE.Exp
toHSE (TVar v) = HSE.Var (HSE.UnQual (HSE.Ident v))
toHSE (TConstr constr ts) =
    foldl' (\e t -> HSE.App e (toHSE t)) (HSE.Con (HSE.UnQual (HSE.Ident constr))) ts
toHSE (TApp v0 vs) =
    foldl' (\e v -> HSE.App e (HSE.Var (HSE.UnQual (HSE.Ident v))))
           (HSE.Var (HSE.UnQual (HSE.Ident v0))) vs
toHSE (TCase v ps) = HSE.Case (toHSE (TVar v)) $ flip map ps $ \(Pat c vs, rhs) ->
                       HSE.Alt dummyLoc
                               (HSE.PApp (HSE.UnQual $ HSE.Ident c)
                                         (map (HSE.PVar . HSE.Ident) vs))
                               (HSE.UnGuardedRhs $ toHSE rhs)
                               (HSE.BDecls [])

ppTTerm :: TTerm -> String
ppTTerm = HSE.prettyPrint . toHSE

ppFn :: (Var, ([Var], TTerm)) -> String
ppFn (fName, (args, body)) = HSE.prettyPrint $ HSE.FunBind
    [ HSE.Match dummyLoc (HSE.Ident fName) (map (HSE.PVar . HSE.Ident) args) Nothing
                (HSE.UnGuardedRhs $ toHSE body) (HSE.BDecls []) ]

dummyLoc :: HSE.SrcLoc
dummyLoc = HSE.SrcLoc "" 0 0

append_str :: String
append_str = unlines
  [ "case xs of"
  , "  Nil -> ys"
  , "  Cons x xs -> Cons x (append xs ys)"
  ]

--

simplTerm :: M.Map Var ([Var], TTerm) -> TTerm -> TTerm
simplTerm _ v@TVar{} = v
simplTerm env tt@(TApp f as) =
    case M.lookup f env of
      Nothing -> tt
      Just (as', TApp f' as'') ->
        let m = zip as' as in
        simplTerm env $ TApp f' $ map (\v -> fromMaybe v (lookup v m)) as''
      Just _ -> tt
simplTerm env (TConstr c ts) = TConstr c $ map (simplTerm env) ts
simplTerm env (TCase v cases) = TCase v $ flip map cases $
    \(Pat c as, rhs) -> (Pat c as, simplTerm (foldl' (flip M.delete) env as) rhs)

simplDefs :: [(Var, [Var], TTerm)] -> TTerm -> (M.Map Var ([Var], TTerm) , TTerm)
simplDefs ds term =
    let ds' = M.fromList $ map (\(f, as, body) -> (f, (as, body))) ds in
    (M.map (\(as, body) -> (as, simplTerm (foldl' (flip M.delete) ds' as) body)) ds'
    ,simplTerm ds' term)

lookupDef :: Var -> [(Var, [Var], TTerm)] -> Maybe (Var, [Var], TTerm)
lookupDef v = lookup v . map (\h@(f,_,_) -> (f, h))

gc :: M.Map Var ([Var], TTerm) -> TTerm -> M.Map Var ([Var], TTerm)
gc env0 root =
    closure (M.fromList $ lookupVs $ S.toList $ fvsTT root)
  where
    lookupVs = mapMaybe (\v -> (v,) <$> M.lookup v env0)

    closure :: M.Map Var ([Var], TTerm) -> M.Map Var ([Var], TTerm)
    closure env =
      let fvs = S.toList $ S.unions $ map (fvsTT . snd . snd) $ M.toList env
          env' = M.fromList $ lookupVs fvs
       in if M.size env' == M.size env then env else closure env'

deleteDef :: Var -> [(Var, [Var], TTerm)] -> [(Var, [Var], TTerm)]
deleteDef _ [] = []
deleteDef v (d@(v', _, _) : rest)
  | v == v'   = rest
  | otherwise = d : deleteDef v rest

main :: IO ()
main = do
    let (decls1, pgm1) = uncurry simplDefs $ deforest' append_pgm
        (decls2, pgm2) = uncurry simplDefs $ deforest' flip_pgm
    forM_ (M.toList $ gc decls1 pgm1) $ putStrLn . ppFn
    putStrLn $ ppTTerm pgm1
    putStrLn "~~~~~~~~~~~~~~~~~~~~~"
    forM_ (M.toList $ gc decls2 pgm2) $ putStrLn . ppFn
    putStrLn $ ppTTerm pgm2
