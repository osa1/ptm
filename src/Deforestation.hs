{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Deforestation where

import Data.Bifunctor (second)
import Data.List (foldl')
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import qualified Data.Set as S

type Var = String
type Constr = String

data Term
  = Var Var
  | Constr Constr [Term]
  | App Var [Term]
  | Case Term [(Pat, Term)]
  deriving (Show)

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

deforest :: Env -> Term -> TTerm
-- rule 1
deforest _   (Var v) = TVar v
-- rule 2
deforest env (Constr c ts) = TConstr c $ map (deforest env) ts
-- rule 3
deforest env t@(App v ts) =
    let Fn args body = lookupFn env v
     in if length args /= length ts
          then error "Function arity doesn't match with # applied arguments"
          else
            -- Linearity means that each argument is used once in the body. This
            -- is how we guarantee that there won't be work duplication.
            -- TODO: We don't check for it though. How to guarantee that there
            -- won't be work duplication?

            -- Careful with capturing here. Example case to be careful:
            --   (\x y -> ...) (... y ...) (...)
            let args' = take (length args) (freshIn $ fvsTerm t)
             in deforest env $ substTerms args' ts (substTerms args (map Var args') body)
-- rule 4
deforest env (Case (Var v) cases) = TCase v $ map (second $ deforest env) cases
-- rule 5
deforest env (Case (Constr c ts) cases) =
    let (vs, rhs) = findCase cases
     in deforest env $ substTerms vs ts rhs
  where
    findCase [] = error $ "Can't find matching case for " ++ show c
    findCase ((Pat con vs, rhs) : cs)
      | c == con  = (vs, rhs)
      | otherwise = findCase cs
-- rule 6
deforest env t@(Case (App f ts) cases) =
    let Fn args body = lookupFn env f
     in if length args /= length ts
          then error "Function arity doesn't match with # applied arguments"
          else
            -- see comments in rule (3)
            let args' = take (length args) (freshIn $ fvsTerm t)
             in deforest env $
                  Case (substTerms args' ts (substTerms args (map Var args') body)) cases
-- rule 7
deforest env tm@(Case (Case t cases) cases') =
    -- we should rename pattern variables in inner case to avoid capturing
    -- variables in outer case's RHSs (see also comments in CoreLike.Simplify
    -- for an example case)

    -- use vsTerm instead of fvsTerm for clarity
    let freshs = freshIn (vsTerm tm) in
    deforest env $ Case t $ flip map cases $ \(p@(Pat _ vs), rhs) ->
      let renamings  = zip vs freshs
          (p', rhs') = renamePat renamings (p, rhs)
       in (p', Case rhs' cases')

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

fvsTerm :: Term -> S.Set Var
fvsTerm (Var v) = S.singleton v
fvsTerm (Constr _ ts) = S.unions $ map fvsTerm ts
fvsTerm (App v ts) = S.insert v $ S.unions $ map fvsTerm ts
fvsTerm (Case t cases) = S.unions $ fvsTerm t : map fvsCase cases

fvsCase :: (Pat, Term) -> S.Set Var
fvsCase (Pat _ vs, rhs) = fvsTerm rhs `S.difference` S.fromList vs

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
    [ (Pat "Leaf" ["z"], Var "z")
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
deforest' = deforest testEnv

main = print $ deforest' append_pgm
