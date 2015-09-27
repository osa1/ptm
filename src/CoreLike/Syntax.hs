{-# LANGUAGE DeriveAnyClass #-}

module CoreLike.Syntax where

import Data.Bifunctor (second)
import Data.Binary (Binary)
import Data.List (foldl')
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import GHC.Generics (Generic)

import Prelude hiding (LT)

type Var = String

type DataCon = String

data PrimOpOp = Add | Sub | Mul | Div | Mod | Eq | LT | LTE
  deriving (Show, Eq, Ord, Generic, Binary)

type Arity = Int

data PrimOp' = PrimOp' PrimOpOp Arity
  deriving (Show, Eq, Ord, Generic, Binary)

data AltCon
  = DataAlt DataCon [Var]
  | LiteralAlt Literal
  | DefaultAlt (Maybe Var)
  deriving (Show, Eq, Ord, Generic, Binary)

data Literal
  = Int Integer
  | Char Char
  deriving (Show, Eq, Ord, Generic, Binary)

data Term ann
  = Var ann Var
  | PrimOp ann PrimOp'
  | Value ann (Value ann)

  | App ann (Term ann) (Term ann)
    -- I'm not convinced about necessity of A-normal form terms, so here I'm
    -- moving back to non-ANF terms. I'll make this A-normal form if this causes
    -- too much trouble. (NB. Add a NOTE describing why go ANF if that happens)

  | Case ann (Term ann) [(AltCon, Term ann)]
  | LetRec ann [(Var, Term ann)] (Term ann)
  deriving (Show, Eq, Ord, Generic, Binary)

data Value ann
  = Lambda ann Var (Term ann)
  | Data ann DataCon [Term ann]
    -- Similar to the `App` case above, using non-ANF terms here.
  | Literal ann Literal
  deriving (Show, Eq, Ord, Generic, Binary)

type Env ann = M.Map Var (Term ann)

-- | Used to generate HSE symbols.
primOpStr :: PrimOpOp -> String
primOpStr Add = "+"
primOpStr Sub = "-"
primOpStr Mul = "*"
primOpStr Div = "/"
primOpStr Mod = "%"
primOpStr Eq  = "=="
primOpStr LT  = "<"
primOpStr LTE = "<="

--------------------------------------------------------------------------------
-- * Working with annotations

setAnn :: ann -> Term ann -> Term ann
setAnn a (Var _ v) = Var a v
setAnn a (PrimOp _ p) = PrimOp a p
setAnn a (Value _ v) = Value a v
setAnn a (App _ t1 t2) = App a t1 t2
setAnn a (Case _ t cs) = Case a t cs
setAnn a (LetRec _ bs t) = LetRec a bs t

getAnn :: Term ann -> ann
getAnn (Var a _) = a
getAnn (PrimOp a _) = a
getAnn (Value a _) = a
getAnn (App a _ _) = a
getAnn (Case a _ _) = a
getAnn (LetRec a _ _) = a

--------------------------------------------------------------------------------
-- * Definition of tags and type synonyms for tagged terms

type Tag = Int

type TaggedTerm = Term Tag
type TaggedValue = Value Tag

type Term' = Term ()
type Value' = Value ()

--------------------------------------------------------------------------------
-- * Collecting free variables

fvsTerm :: Term ann -> S.Set Var
fvsTerm (Var _ v) = S.singleton v
fvsTerm PrimOp{} = S.empty
fvsTerm (Value _ val) = fvsVal val
fvsTerm (App _ t1 t2) = fvsTerm t1 `S.union` fvsTerm t2
fvsTerm (Case _ tm cases) = S.unions $ fvsTerm tm : map fvsCase cases
fvsTerm (LetRec _ bindings body) =
    free `S.union` (fvsTerm body `S.difference` bound)
  where
    (bound, free) = fvsBindings bindings

fvsVal :: Value ann -> S.Set Var
fvsVal (Lambda _ arg body) = S.delete arg $ fvsTerm body
fvsVal (Data _ _ args) = S.unions $ map fvsTerm args
fvsVal Literal{} = S.empty

fvsCase :: (AltCon, Term ann) -> S.Set Var
fvsCase (DataAlt _ args, rhs) = fvsTerm rhs `S.difference` S.fromList args
fvsCase (LiteralAlt{}, rhs) = fvsTerm rhs
fvsCase (DefaultAlt Nothing, rhs) = fvsTerm rhs
fvsCase (DefaultAlt (Just v), rhs) = S.delete v $ fvsTerm rhs

fvsBindings :: [(Var, Term ann)] -> (S.Set Var, S.Set Var)
fvsBindings bs =
    (binds, rhss `S.difference` binds)
  where
    binds = S.fromList $ map fst bs
    rhss  = S.unions $ map (fvsTerm . snd) bs

--------------------------------------------------------------------------------
-- * Renaming variables
--
-- This is like a substitution, except we only substitute for variables and we
-- don't change annotations.

renameTerm :: Var -> Var -> Term ann -> Term ann
renameTerm v1 v2 t@(Var ann v)
    | v == v1   = Var ann v2
    | otherwise = t
renameTerm _  _ t@PrimOp{} = t
renameTerm v1 v2 (Value ann v) = Value ann $ renameValue v1 v2 v
renameTerm v1 v2 (App ann t1 t2) = App ann (renameTerm v1 v2 t1) (renameTerm v1 v2 t2)
renameTerm v1 v2 (Case ann t cs) = Case ann (renameTerm v1 v2 t) (map (renameCase v1 v2) cs)
renameTerm v1 v2 t@(LetRec ann bs body)
    | v1 `elem` map fst bs = t
    | v2 `elem` map fst bs =
        let
          freshBinder = freshFor (S.insert v1 $ S.insert v2 $ vars t)
          bs'         = renameWBinders [(v2, freshBinder)] bs
          body'       = renameTerm v2 freshBinder body
        in
          renameTerm v1 v2 (LetRec ann bs' body')
    | otherwise =
        LetRec ann (map (second (renameTerm v1 v2)) bs) (renameTerm v1 v2 body)

-- FIXME: This is a weird name, it sounds like we're renaming multiple terms,
-- which is not the case.
renameTerms :: [(Var, Var)] -> Term ann -> Term ann
renameTerms bs t = foldl' (\t1 (v, t') -> renameTerm v t' t1) t bs

renameValue :: Var -> Var -> Value ann -> Value ann
renameValue v1 v2 v@(Lambda ann b t)
    | v1 == b = v
    | v2 == b =
        let
          freshBinder = freshFor (S.insert v1 $ S.insert v2 $ valVars v)
          t' = renameTerm b freshBinder t
        in
          renameValue v1 v2 (Lambda ann freshBinder t')
    | otherwise =
        Lambda ann b (renameTerm v1 v2 t)

renameValue v1 v2 (Data ann con args) =
    Data ann con (map (renameTerm v1 v2) args)

renameValue _ _ l@Literal{} = l

renameCase :: Var -> Var -> (AltCon, Term ann) -> (AltCon, Term ann)
renameCase v1 v2 c@(DataAlt con vs, rhs)
    | v1 `elem` vs = c
    | v2 `elem` vs =
        let
          freshBinder = freshFor (S.insert v1 $ S.insert v2 $ S.fromList vs `S.union` vars rhs)
          vs' = map (\v -> if v == v2 then freshBinder else v) vs
          rhs' = renameTerm v2 freshBinder rhs
        in
          renameCase v1 v2 (DataAlt con vs', rhs')
    | otherwise =
        (DataAlt con vs, renameTerm v1 v2 rhs)
renameCase v1 v2 (l@LiteralAlt{}, rhs) = (l, renameTerm v1 v2 rhs)
renameCase v1 v2 (l@(DefaultAlt Nothing), rhs) = (l, renameTerm v1 v2 rhs)
renameCase v1 v2 (l@(DefaultAlt (Just v)), rhs)
    | v == v1 = (l, rhs)
    | v == v2 =
        let
          freshBinder = freshFor (S.insert v1 $ S.insert v2 $ vars rhs)
        in
          renameCase v1 v2 (DefaultAlt (Just freshBinder), renameTerm v freshBinder rhs)
    | otherwise =
        (l, renameTerm v1 v2 rhs)

renameWBinders :: [(Var, Var)] -> [(Var, Term ann)] -> [(Var, Term ann)]
renameWBinders _ [] = []
renameWBinders rns ((v, t) : br) =
    (fromMaybe v (lookup v rns), renameTerms rns t) : renameWBinders rns br

renameVars :: [(Var, Var)] -> Var -> Var
renameVars vs v
    | Just v' <- lookup v vs = v'
    | otherwise = v

--------------------------------------------------------------------------------
-- * Substitutions

substTerm :: Var -> Term ann -> Term ann -> Term ann
substTerm v' t' t@(Var _ v)
    | v == v'   = t'
    | otherwise = t
substTerm _ _ p@PrimOp{} = p
substTerm v t (Value ann val) = Value ann $ substVal v t val
substTerm v t (App ann t1 t2) = App ann (substTerm v t t1) (substTerm v t t2)
substTerm v t (Case ann scrt cases) = Case ann (substTerm v t scrt) (map (substCase v t) cases)
substTerm v t l@(LetRec ann bndrs body)
    | v `S.member` bndr_vs = l
    | not (S.null need_renaming) =
        let
          rns = zip (S.toList need_renaming) (freshVarsFor $ S.insert v $ vars l `S.union` vars t)
          bndrs' = renameWBinders rns bndrs
          body'  = renameTerms rns body
        in
          substTerm v t (LetRec ann bndrs' body')
    | otherwise = LetRec ann (map (second (substTerm v t)) bndrs) (substTerm v t body)
  where
    t_vs = fvsTerm t
    bndr_vs = S.fromList (map fst bndrs)
    need_renaming = t_vs `S.intersection` bndr_vs

-- FIXME: Rename this(similar to renameTerms).
substTerms :: [(Var, Term ann)] -> Term ann -> Term ann
substTerms bs t = foldl' (\t1 (v, t') -> substTerm v t' t1) t bs

substVal :: Var -> Term ann -> Value ann -> Value ann
substVal v t l@(Lambda ann b body)
    | v == b = l
    | b `S.member` fvsTerm t =
        let
          b' = freshFor (S.insert v $ vars t `S.union` valVars l)
          body' = renameTerm b b' body
        in
          substVal v t (Lambda ann b' body')
    | otherwise =
        Lambda ann b (substTerm v t body)
substVal v t (Data ann con args) =
    Data ann con $ map (substTerm v t) args
substVal _ _ l@Literal{} = l

substCase :: Var -> Term ann -> (AltCon, Term ann) -> (AltCon, Term ann)
substCase v t c@(d@(DataAlt con vs), rhs)
    | v `elem` vs = c
    | not (S.null need_renaming) =
        let
          rns = zip (S.toList need_renaming)
                    (freshVarsFor $ v `S.insert` vars t `S.union` S.fromList vs `S.union` vars rhs)
          vs' = map (renameVars rns) vs
          rhs' = renameTerms rns rhs
        in
          substCase v t (DataAlt con vs', rhs')
    | otherwise = (d, substTerm v t rhs)
  where
    need_renaming = fvsTerm t `S.intersection` S.fromList vs
substCase v t (l@LiteralAlt{}, rhs) = (l, substTerm v t rhs)
substCase v t (d@(DefaultAlt Nothing), rhs) = (d, substTerm v t rhs)
substCase v t c@(d@(DefaultAlt (Just v')), rhs)
    | v == v' = c
    | v' `elem` fvsTerm t =
        let
          v'' = freshFor (S.insert v $ S.insert v' $ vars t `S.union` vars rhs)
          rhs' = renameTerm v' v'' rhs
        in
          substCase v t (DefaultAlt (Just v''), rhs')
    | otherwise = (d, substTerm v t rhs)

--------------------------------------------------------------------------------
-- * Collecting variables
--
-- We use this when generating fresh names. Even though `fvsTerm` is enough for
-- fresh variable generation, we use these generate not-used names for
-- readability.

-- | Collect all variables used in given term, free or not.
vars :: Term ann -> S.Set Var
vars (Var _ v) = S.singleton v
vars PrimOp{} = S.empty
vars (Value _ val) = valVars val
vars (App _ t1 t2) = vars t1 `S.union` vars t2
vars (Case _ t cs) = S.unions $ vars t : map altConVars (map fst cs) ++ map vars (map snd cs)
vars (LetRec _ bs rhs) = S.unions $ vars rhs : S.fromList (map fst bs) : map (vars . snd) bs

valVars :: Value ann -> S.Set Var
valVars (Lambda _ arg body) = S.insert arg $ vars body
valVars (Data _ _ args) = S.unions $ map vars args
valVars Literal{} = S.empty

altConVars :: AltCon -> S.Set Var
altConVars (DataAlt _ vs) = S.fromList vs
altConVars LiteralAlt{} = S.empty
altConVars (DefaultAlt mv) = maybe S.empty S.singleton mv

vars' :: [Term ann] -> S.Set Var
vars' = S.unions . map vars

--------------------------------------------------------------------------------
-- * Generating fresh variables

-- | Come up with a var that's not used in given term.
freshInTerm :: Term ann -> Var
freshInTerm = freshFor . vars

-- | Come up with an infinite list of vars that are not used in given term.
freshVarsInTerm :: Term ann -> [Var]
freshVarsInTerm = freshVarsFor . vars

freshVarsInVal :: Value ann -> [Var]
freshVarsInVal = freshVarsFor . valVars

-- | Come up with a var that's not in the given list of vars.
freshFor :: S.Set Var -> Var
freshFor = head . freshVarsFor

-- | Come up with an infinite list of vars that are not in the given set of
-- vars.
freshVarsFor :: S.Set Var -> [Var]
freshVarsFor used =
    filter (not . (`S.member` used)) supply
  where
    supply = map (('f' :) . show) [0 :: Int ..]

-- | Similar with 'freshVarsFor', but returns names with given prefix.
freshVarsForPfx :: String -> S.Set Var -> [Var]
freshVarsForPfx s used =
    filter (not . (`S.member` used)) supply
  where
    supply = map ((s ++) . show) [0 :: Int ..]

freshForPfx :: String -> S.Set Var -> Var
freshForPfx s = (s ++) . head . freshVarsFor
