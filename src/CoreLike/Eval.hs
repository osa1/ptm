{-# LANGUAGE TupleSections #-}

module CoreLike.Eval where

import Data.List (foldl')
import qualified Data.Map.Strict as M

import CoreLike.Syntax

type Env = M.Map Var Term

data StackFrame
  = Apply Var
  | Scrutinise [(AltCon, Term)]
  | PrimApply PrimOp [Value] [Term]
  | Update Var
  deriving (Show)

type Stack = [StackFrame]

type State = (Term, Env, Stack)

mapVars :: [(Var, Term)] -> Env -> Env
mapVars = flip $ foldl' (\env (v, t) -> M.insert v t env)

evalStep :: State -> Maybe State
evalStep (Var v, env, stack) = (, M.delete v env, Update v : stack) <$> M.lookup v env
evalStep (Value v, env, stack) = unwind v env stack
evalStep (App t v, env, stack) = Just (t, env, Apply v : stack)
evalStep (PrimOp op (arg1 : args), env, stack) =
    Just (arg1, env, PrimApply op [] args : stack)
evalStep (PrimOp op [], _, _) = error $ "evalStep: PrimOp without arguments: " ++ show op
evalStep (Case scr cases, env, stack) = Just (scr, env, Scrutinise cases : stack)
evalStep (LetRec binds rhs, env, stack) = Just (rhs, mapVars binds env, stack)

unwind :: Value -> Env -> Stack -> Maybe State
unwind _ _ [] = Nothing
unwind val env (Update var : stack) = Just (Value val, M.insert var (Value val) env, stack)
unwind (Lambda arg body) env (Apply v : stack) =
    Just (body, M.insert arg (Var v) env, stack)
unwind v@(Data con args) env (Scrutinise cases : stack) = findCase cases
  where
    findCase :: [(AltCon, Term)] -> Maybe State
    findCase [] = Nothing
    findCase ((DataAlt con' args', rhs) : rest)
      | con == con' = Just (rhs, mapVars (zip args' (map Var args)) env, stack)
      | otherwise   = findCase rest
    findCase ((LiteralAlt{}, _) : rest) = findCase rest
    findCase ((DefaultAlt Nothing, rhs) : _) = Just (rhs, env, stack)
    findCase ((DefaultAlt (Just d), rhs) : _) = Just (rhs, M.insert d (Value v) env, stack)
unwind v@(Literal lit) env (Scrutinise cases : stack) = findCase cases
  where
    findCase :: [(AltCon, Term)] -> Maybe State
    findCase [] = Nothing
    findCase ((DataAlt{}, _) : rest) = findCase rest
    findCase ((LiteralAlt lit', rhs) : rest)
      | lit == lit' = Just (rhs, env, stack)
      | otherwise   = findCase rest
    findCase ((DefaultAlt Nothing, rhs) : _) = Just (rhs, env, stack)
    findCase ((DefaultAlt (Just d), rhs) : _) = Just (rhs, M.insert d (Value v) env, stack)
unwind v env (PrimApply op vals [] : stack) =
    Just . (, env, stack) . Value $ applyPrimOp op (vals ++ [v])
unwind v env (PrimApply op vals (t : ts) : stack) =
    Just (t, env, PrimApply op (vals ++ [v]) ts : stack)
unwind v _ s =
    error $ "unwind: Found ill-typed term, is this a bug?\n"
            ++ "value: " ++ show v ++ "stack: " ++ show s

applyPrimOp :: PrimOp -> [Value] -> Value
applyPrimOp Add [Literal (Int i1), Literal (Int i2)] =
    Literal $ Int $ i1 + i2
applyPrimOp Subtract [Literal (Int i1), Literal (Int i2)] =
    Literal $ Int $ i1 - i2
applyPrimOp Multiply [Literal (Int i1), Literal (Int i2)] =
    Literal $ Int $ i1 * i2
applyPrimOp Divide [Literal (Int i1), Literal (Int i2)] =
    Literal $ Int $ i1 `div` i2
applyPrimOp Modulo [Literal (Int i1), Literal (Int i2)] =
    Literal $ Int $ i1 `mod` i2
applyPrimOp Equal [Literal (Int i1), Literal (Int i2)] =
    Data (if i1 == i2 then "True" else "False") []
applyPrimOp op lits = error $ "Unhandled PrimOp " ++ show op ++ " args: " ++ show lits
