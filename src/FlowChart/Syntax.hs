module FlowChart.Syntax where

import Data.String (IsString (..))

type Var = String

data Program
  = -- INVARIANT: At least one block
    Program [Var] [BasicBlock]
  deriving (Show, Eq)

type Label = String

data BasicBlock
  = BasicBlock Label [Assignment] (Maybe Jump)
  deriving (Show, Eq)

data Assignment
  = Assignment Var Expr
  deriving (Show, Eq)

data Jump
  = Goto Label
  | If Expr Label Label
  | Halt
  | Panic Expr
  deriving (Show, Eq)

data Expr
  = Constant Constant
  | Var Var
  | Op Op [Expr]
  deriving (Show, Eq)

type Constant = Val

data Op
  = Hd | Tl | Cons | Read | Eq
  | Rest | FirstInstruction | FirstSym | NewTail
  deriving (Show, Eq)

data Val
  = VSymbol String
  | VList [Val]
  deriving (Show, Eq, Ord)

instance IsString Val where
    fromString = VSymbol
