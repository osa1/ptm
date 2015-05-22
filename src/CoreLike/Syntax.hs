module CoreLike.Syntax where

import Control.Arrow (second)
import Data.List (delete, foldl', intersect, (\\))
import Data.Maybe (fromMaybe)
import qualified Data.Set as S

type Var = String

type DataCon = String

data PrimOp = Add | Sub | Mul | Div | Mod | Eq | LT | LTE
  deriving (Show, Eq, Ord)

data AltCon
  = DataAlt DataCon [Var]
  | LiteralAlt Literal
  | DefaultAlt (Maybe Var)
  deriving (Show, Eq, Ord)

data Literal
  = Int Integer
  | Char Char
  deriving (Show, Eq, Ord)

data Term
  = Var Var
  | Value Value
  | App Term Var
  | PrimOp PrimOp [Term] -- TODO: Why isn't this in ANF?
  | Case Term [(AltCon, Term)]
  | LetRec [(Var, Term)] Term
  deriving (Show, Eq, Ord)

data Value
  = Lambda Var Term
  | Data DataCon [Var]
  | Literal Literal
  -- This is needed for call-by-need evaluation
  -- | Indirect Var
  deriving (Show, Eq, Ord)

------------------------------
-- * Collecting free variables

fvsTerm :: Term -> S.Set Var
fvsTerm (Var v) = S.singleton v
fvsTerm (Value val) = fvsVal val
fvsTerm (App tm v) = S.insert v $ fvsTerm tm
fvsTerm (PrimOp _ ts) = S.unions $ map fvsTerm ts
fvsTerm (Case tm cases) = S.unions $ fvsTerm tm : map fvsCase cases
fvsTerm (LetRec bindings body) =
    let (bound, free) = fvsBindings bindings
     in free `S.union` (fvsTerm body `S.difference` bound)

fvsVal :: Value -> S.Set Var
fvsVal (Lambda arg body) = S.delete arg $ fvsTerm body
fvsVal (Data _ args) = S.fromList args
fvsVal Literal{} = S.empty

fvsCase :: (AltCon, Term) -> S.Set Var
fvsCase (DataAlt _ args, rhs) = fvsTerm rhs `S.difference` S.fromList args
fvsCase (LiteralAlt{}, rhs) = fvsTerm rhs
fvsCase (DefaultAlt Nothing, rhs) = fvsTerm rhs
fvsCase (DefaultAlt (Just v), rhs) = S.delete v $ fvsTerm rhs

fvsBindings :: [(Var, Term)] -> (S.Set Var, S.Set Var)
fvsBindings bs =
    let binds = S.fromList $ map fst bs
        rhss  = S.unions $ map (fvsTerm . snd) bs
     in (binds, rhss `S.difference` binds)

------------------
-- * Substitutions

substTerm :: Var -> Term -> Term -> Term
substTerm v' t' t@(Var v)
    | v == v'   = t'
    | otherwise = t
substTerm v' t' (Value v) = substVal v' t' v
substTerm v' t' (App t v)
    | v == v'   =
        case t' of
          Var newVar -> App (substTerm v' t' t) newVar
          _          -> LetRec [(v', t')] $ App (substTerm v' t' t) v'
    | otherwise =
        App (substTerm v' t' t) v
substTerm v' t' (PrimOp op ts) = PrimOp op $ map (substTerm v' t') ts
substTerm v' t' (Case t cases) = Case (substTerm v' t' t) (map (substCase v' t') cases)
substTerm v' t' lr@(LetRec binds rhs) =
    if v' `elem` map fst binds
      then lr
      else
        let
           t'fvs = S.toList $ fvsTerm t'
           renamings = zip
             -- free variables in t' that will be bound after substitutions
             (intersect (map fst binds) t'fvs)
             -- fresh names given to binders of t'fvs
             (freshVarsInTerm lr)
           binds' = renameWBinders binds renamings
           -- TODO: `map (second Var) renamings` parts is generated multiple
           -- times. (also in Simplify)
           rhs'   = substTerms (map (second Var) renamings) rhs
         in
           LetRec (map (second (substTerm v' t')) binds') (substTerm v' t' rhs')

substTerms :: [(Var, Term)] -> Term -> Term
substTerms bs t = foldl' (\t1 (v, t') -> substTerm v t' t1) t bs

substCase :: Var -> Term -> (AltCon, Term) -> (AltCon, Term)
substCase v' t' alt@(d@(DataAlt con args), rhs)
    | v' `elem` args = alt
    | otherwise =
        -- TODO: Test this code
        let t'fvs      = fvsTerm t'
            captured   = args `intersect` S.toList t'fvs
            renamings  = zip captured (freshVarsFor $ altConVars d `S.union` vars rhs)
            renamings' = map (second Var) renamings

            renameBs :: [Var] -> [(Var, Var)] -> [Var]
            renameBs []       _  = []
            renameBs (v : vs) rs = fromMaybe v (lookup v rs) : renameBs vs rs
         in
           if null captured
              then (DataAlt con args, substTerm v' t' rhs)
              else substCase v' t' (DataAlt con (renameBs args renamings), substTerms renamings' rhs)

substCase v' t' (l@LiteralAlt{}, rhs) = (l, substTerm v' t' rhs)
substCase v' t' (DefaultAlt Nothing, rhs) = (DefaultAlt Nothing, substTerm v' t' rhs)
substCase v' t' alt@(DefaultAlt (Just v), rhs)
    | v == v'   = alt
    | v `elem` fvsTerm t' =
        -- TODO: test this code
        let newv = head $ delete v (freshVarsInTerm rhs)
         in substCase v' t' (DefaultAlt (Just newv), substTerm v (Var newv) rhs)
    | otherwise = (DefaultAlt (Just v), substTerm v' t' rhs)

substVal :: Var -> Term -> Value -> Term
substVal v' t' l@(Lambda v t)
    | v == v'   = Value l
    | v `S.member` fvsTerm t' =
        let vf = freshInTerm (Value l)
         in substVal v' t' (Lambda vf (substTerm v (Var vf) t))
    | otherwise =
        Value $ Lambda v (substTerm v' t' t)
substVal v' t' d@(Data con args)
    | v' `elem` args =
        case t' of
          Var newV -> Value $ Data con $ map (\a -> if a == v' then newV else a) args
          _        -> LetRec [(v', t')] $ Value $ Data con args
    | otherwise = Value d
substVal _  _  l@Literal{} = Value l

renameWBinders :: [(Var, Term)] -> [(Var, Var)] -> [(Var, Term)]
renameWBinders [] _ = []
renameWBinders ((v, t) : br) rns =
  (fromMaybe v (lookup v rns), substTerms (map (second Var) rns) t) : renameWBinders br rns

-- | Collect all variables used in given term, free or not.
vars :: Term -> S.Set Var
vars (Var v) = S.singleton v
vars (Value (Lambda arg body)) = S.insert arg $ vars body
vars (Value (Data _ vs)) = S.fromList vs
vars (Value Literal{}) = S.empty
vars (App t v) = S.insert v $ vars t
vars (PrimOp _ args) = S.unions $ map vars args
vars (Case t cs) = S.unions $ vars t : map altConVars (map fst cs) ++ map vars (map snd cs)
vars (LetRec bs rhs) = S.unions $ vars rhs : S.fromList (map fst bs) : map (vars . snd) bs

altConVars :: AltCon -> S.Set Var
altConVars (DataAlt _ vs) = S.fromList vs
altConVars LiteralAlt{} = S.empty
altConVars (DefaultAlt mv) = maybe S.empty S.singleton mv

vars' :: [Term] -> S.Set Var
vars' = S.unions . map vars

-- | Come up with a var that's not used in given term.
freshInTerm :: Term -> Var
freshInTerm t = freshFor (vars t)

-- | Cope up with an infinite list of vars that are not used in given term.
freshVarsInTerm :: Term -> [Var]
freshVarsInTerm t = freshVarsFor (vars t)

-- | Come up with a var that's not in the given list of vars.
freshFor :: S.Set Var -> Var
freshFor vs = head $ freshVarsFor vs

-- | Come up with an infinite list of vars that are not in the given set of
-- vars.
freshVarsFor :: S.Set Var -> [Var]
freshVarsFor used =
    filter (not . (`S.member` used)) supply
  where
    supply = map (('f' :) . show) [0..]

-- | Similar with 'freshVarsFor', but returns names with given prefix.
freshVarsForPfx :: String -> S.Set Var -> [Var]
freshVarsForPfx s used =
    filter (not . (`S.member` used)) supply
  where
    supply = map ((s ++) . show) [0..]

freshForPfx :: String -> S.Set Var -> Var
freshForPfx s used = (s ++) $ head $ freshVarsFor used
