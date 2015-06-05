{-# LANGUAGE DeriveAnyClass, DeriveGeneric #-}

module Deforestation.Syntax where

import Control.DeepSeq (NFData)
import Data.Bifunctor (second)
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import Data.String (IsString (..))
import GHC.Generics (Generic)

type Var = String
type Constr = String

data Term
  = Var Var
  | Constr Constr [Term]
  | App Var [Term]
  | Case Term [(Pat, Term)]
  deriving (Show, Generic, NFData)

instance IsString Term where
    fromString = Var

data Pat = Pat Constr [Var]
  deriving (Show, Generic, NFData)

data TTerm
  = TVar Var
  | TConstr Constr [TTerm]
  | TApp Var [Var]
  | TCase Var [(Pat, TTerm)]
  deriving (Show, Generic, NFData)

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
