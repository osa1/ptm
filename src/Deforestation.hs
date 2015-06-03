{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections #-}

module Deforestation where

import Control.Monad.State.Strict
import Data.Bifunctor (second)
import Data.List (deleteBy, foldl')
import qualified Data.Map as M
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Set as S
import Data.String (IsString (..))

-- import Debug.Trace

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

-- we only keep track of applications
type History = [(Var, [Term], Var {- function name -})]

deforest :: Env -> Term -> State History TTerm
-- rule 1
deforest _   (Var v) = trace "rule 1" $ return $ TVar v
-- rule 2
deforest env (Constr c ts) = trace "rule 2" $ TConstr c <$> mapM (deforest env) ts
-- rule 3
deforest env t@(App v ts) = trace "rule 3" $ do
    history <- get
    case checkRenaming (v, ts) history of
      Just tt -> return tt
      Nothing -> do
        let Fn args body = lookupFn env v
        modify ((v, ts, 'h' : show (length history)) :)
        if length args /= length ts
          then error "Function arity doesn't match with # applied arguments"
          else
            -- Linearity means that each argument is used once in the body. This
            -- is how we guarantee that there won't be work duplication.
            -- TODO: We don't check for it though. How to guarantee that there
            -- won't be work duplication?

            -- Careful with capturing here. Example case to be careful:
            --   (\x y -> ...) (... y ...) (...)
            let args' = take (length args) (freshIn $ fvsTerm t) in
            deforest env $ substTerms args' ts (substTerms args (map Var args') body)
-- rule 4
deforest env (Case (Var v) cases) = trace "rule 4" $
    TCase v <$> mapM (\(p, r) -> (p,) <$> deforest env r) cases
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
deforest env t@(Case (App f ts) cases) = trace "rule 6" $
    let Fn args body = lookupFn env f in
    if length args /= length ts
      then error "Function arity doesn't match with # applied arguments"
      else
        -- see comments in rule (3)
        let args' = take (length args) (freshIn $ fvsTerm t)
         in deforest env $
              Case (substTerms args' ts (substTerms args (map Var args') body)) cases
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
isRenaming Case{} Case{} = Nothing -- TODO: Maybe improve this
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

checkRenaming :: (Var, [Term]) -> History -> Maybe TTerm
checkRenaming (fName, args) = iter
  where
    iter [] = Nothing
    iter ((f, as, h) : rest) =
      case isRenaming (App f as) (App fName args) of
        Just substs -> trace ("~~~found renaming:\n" ++ show (App f as) ++ "\n" ++ show (App fName args) ++ "\n" ++ show substs) $ Just $ TApp h (map snd substs)
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
    substCase p@(Pat _ vs, rhs) =
      let captures = S.toList $ S.fromList vs `S.intersection` fvsTerm t
          renamings = zip captures (freshIn (fvsTerm rhs `S.union` S.fromList vs
                                                         `S.union` fvsTerm t))
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

deforest' :: Term -> TTerm
deforest' t = evalState (deforest testEnv t) []

main :: IO ()
main = do
  print $ deforest' append_pgm
  print $ deforest' flip_pgm
