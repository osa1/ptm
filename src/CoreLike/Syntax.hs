module CoreLike.Syntax where

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
fvsVAl Literal{} = S.empty

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
