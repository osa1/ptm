{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving, LambdaCase,
             OverloadedStrings, TupleSections #-}

module Deforestation.Deforest where

import Control.DeepSeq (force)
import Control.Monad.State.Strict
import Data.List (deleteBy, foldl', sortBy, (\\))
import qualified Data.Map as M
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Set as S

import Deforestation.Parser
import Deforestation.Syntax
import Deforestation.ToHSE

-- import qualified Debug.Trace
import Debug.Trace

-- trace :: String -> a -> a
-- trace _ = id

data Fn = Fn [Var] Term deriving (Show)

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

traceRule :: Int -> Term -> a -> a
traceRule i t = trace ("rule " ++ show i ++ " - " ++ ppTerm t)

deforest :: Env -> Term -> State DState TTerm
-- rule 1
deforest _   t@(Var v) = traceRule 1 t $ return $ TVar v
-- rule 2
deforest env t@(Constr c ts) = traceRule 2 t $ TConstr c <$> mapM (deforest env) ts
-- rule 3
deforest env t@(App v ts) = traceRule 3 t $ do
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
deforest env t@(Case (Var v) cases) = traceRule 4 t $ do
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
deforest env t@(Case (Constr c ts) cases) = traceRule 5 t $
    let (vs, rhs) = findCase cases
     in deforest env $ substTerms vs ts rhs
  where
    findCase [] = error $ "Can't find matching case for " ++ show c
    findCase ((Pat con vs, rhs) : cs)
      | c == con  = (vs, rhs)
      | otherwise = findCase cs
-- rule 6
deforest env t@(Case (App f ts) cases) = traceRule 6 t $ do
    -- let Fn args body = lookupFn env f
    -- let fvs = fvsTerm t `S.difference` M.keysSet env
    --     args' = take (length args) (freshIn  fvs)
    -- deforest env $
    --   Case (substTerms args' ts (substTerms args (map Var args') body)) cases
    hist <- gets history
    case checkCaseRenaming (App f ts, cases) hist of
      Just tt -> return tt
      Nothing -> do
        let hName = 'h' : show (length hist)
        modify $ \s -> s{history = ((Match (App f ts) cases, hName) : hist)}
        let Fn args body = lookupFn env f
        if length args /= length ts
          then error "Function arity doesn't match with # applied arguments"
          else do
            -- see comments in rule (3)
            let fvs = fvsTerm t `S.difference` M.keysSet env
                args' = take (length args) (freshIn  fvs)
            ret <- deforest env $
                     Case (substTerms args' ts (substTerms args (map Var args') body)) cases
            modify $ \s -> s{defs = (hName, S.toList fvs, ret) : defs s}
            return $ TApp hName (S.toList fvs)
-- rule 7
deforest env tm@(Case (Case t cases) cases') = traceRule 7 tm $
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
checkCaseRenaming c@(scrt, cases) h0 =
    let h = [ (t, cs, h) | (Match t cs, h) <- h0 ] in
    -- Debug.Trace.trace ("checkCaseRenaming: " ++ show c ++ "\nhistory: " ++ show h) $
      iter h
  where
    iter [] = Nothing -- Debug.Trace.trace "Nothing" Nothing
    iter ((scrt', cases', h) : rest) =
      case isRenaming (Case scrt' cases') (Case scrt cases) of
        Just substs ->
            -- Debug.Trace.trace "Renaming found" $
            Just $ TApp h (map snd $ sortBy (\(v1, _) (v2, _) -> v1 `compare` v2) substs)
        Nothing     -> iter rest

------------------------------------------------
-- * Example functions, programs and environment

append_fn :: Fn
append_fn =
  Fn ["xs", "ys"] $ parseTerm' $ unlines
    [ "case xs of"
    , "  Nil -> ys"
    , "  Cons x xs -> Cons x (append xs ys)"
    ]

reverse_fn :: Fn
reverse_fn =
  Fn ["lst"] $ parseTerm' $ unlines
    [ "case lst of"
    , "  Nil -> Nil"
    , "  Cons x xs -> append (reverse xs) (Cons x Nil)"
    ]

flip_fn :: Fn
flip_fn =
  Fn ["zt"] $ parseTerm' $ unlines
    [ "case zt of"
    , "  Leaf z -> Leaf z"
    , "  Branch xt yt -> Branch (flip yt) (flip zt)"
    ]

testEnv :: Env
testEnv = M.fromList
  [ ("flip", flip_fn)
  , ("append", append_fn)
  , ("reverse", reverse_fn)
  ]

append_pgm :: Term
append_pgm = parseTerm' "append (append xs ys) zs"

append_pgm1 :: Term
append_pgm1 = parseTerm' "append (append (append xs ys) zs) lst"

append_pgm2 :: Term
append_pgm2 = parseTerm' "append xs (append ys zs)"

flip_pgm :: Term
flip_pgm = parseTerm' "flip (flip zt)"

reverse_pgm :: Term
reverse_pgm = parseTerm' "reverse (reverse lst)"

deforest' :: Term -> ([(Var, [Var], TTerm)], TTerm)
deforest' t =
    let (tt, DState _ ds) = runState (deforest testEnv t) (DState [] [])
     in (ds, tt)

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

deforestPrint :: Term -> IO ()
deforestPrint t = do
    -- forcing here to run `Debug.Trace.trace` calls
    -- (also need a bang pattern to not thunk `force` call)
    let !(decls, pgm) = force $ uncurry simplDefs $ deforest' t
    putStrLn "---"
    forM_ (M.toList $ gc decls pgm) $ putStrLn . ppFn
    putStrLn $ ppTTerm pgm
    putStrLn "---"

main :: IO ()
main = mapM_ deforestPrint
    [ append_pgm
    , append_pgm1
    , append_pgm2
    , flip_pgm
    ]
