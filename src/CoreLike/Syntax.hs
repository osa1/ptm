module CoreLike.Syntax where

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
  | Indirect Var
  deriving (Show, Eq, Ord)
