{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections #-}

module Deforestation where

import Control.Monad.State
import Data.Bifunctor (second)
import Data.List (foldl')
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import Data.String (IsString (..))

-- import Debug.Trace

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

type History = [(Var, [Term])] -- we only keep track of applications

deforest :: Env -> Term -> State History TTerm
-- rule 1
deforest _   (Var v) = trace "rule 1" $ return $ TVar v
-- rule 2
deforest env (Constr c ts) = trace "rule 2" $ TConstr c <$> mapM (deforest env) ts
-- rule 3
deforest env t@(App v ts) = trace "rule 3" $ do
    history <- get
    if checkRenaming (v, ts) history
      then return $ TVar "<<loop>>"
      else do
        let Fn args body = lookupFn env v
        modify ((v, ts) :)
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

-- initial implementation, just return bool to blow to whistle
isRenaming :: Term -> Term -> Bool
-- isRenaming t1 t2
--   | trace ("isRenaming: " ++ show t1 ++ " -- " ++ show t2) False = undefined
isRenaming Var{} Var{} = True
isRenaming (Constr c1 ts1) (Constr c2 ts2) =
    c1 == c2 && length ts1 == length ts2 && and (zipWith isRenaming ts1 ts2)
isRenaming (App f1 ts1) (App f2 ts2) =
    f1 == f2 && length ts1 == length ts2 && and (zipWith isRenaming ts1 ts2)
isRenaming Case{} Case{} = False -- TODO: Maybe improve this
isRenaming _ _ = False

checkRenaming :: (Var, [Term]) -> [(Var, [Term])] -> Bool
checkRenaming (fName, args) history =
    or $ map (\(f, as) -> isRenaming (App f as) (App fName args)) history

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
