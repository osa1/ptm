module CoreLike.Syntax where

import Control.Arrow (second)
import qualified Data.Set as S

type Var = String

type DataCon = String

data PrimOp
  = Add | Subtract | Multiply | Divide
  | Modulo | Equal | LessThan | LessThanEqual
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
  | PrimOp PrimOp [Term]
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
    let (bound, free) = fvsBindings bindings in free `S.union` (fvsTerm body `S.difference` bound)

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
       else LetRec (map (second (substTerm v' t')) binds) (substTerm v' t' rhs)

substCase :: Var -> Term -> (AltCon, Term) -> (AltCon, Term)
substCase v' t' alt@(DataAlt con args, rhs)
    | v' `elem` args = alt
    | otherwise = (DataAlt con args, substTerm v' t' rhs)
substCase v' t' (l@LiteralAlt{}, rhs) = (l, substTerm v' t' rhs)
substCase v' t' (DefaultAlt Nothing, rhs) = (DefaultAlt Nothing, substTerm v' t' rhs)
substCase v' t' alt@(DefaultAlt (Just v), rhs)
    | v == v'   = alt
    | otherwise = (DefaultAlt (Just v), substTerm v' t' rhs)

substVal :: Var -> Term -> Value -> Term
substVal v' t' l@(Lambda v t)
    | v == v'   = Value l
    | otherwise = Value $ Lambda v (substTerm v' t' t)
substVal v' t' d@(Data con args)
    | v' `elem` args =
        case t' of
          Var newV -> Value $ Data con $ map (\a -> if a == v' then newV else a) args
          _        -> LetRec [(v', t')] $ Value $ Data con args
    | otherwise = Value d
substVal _  _  l@Literal{} = Value l
