{-# LANGUAGE DeriveAnyClass, DeriveGeneric, LambdaCase, TupleSections #-}

module CoreLike.Eval where

import Data.Binary (Binary)
import Data.List (foldl')
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import GHC.Generics (Generic)

import CoreLike.Parser
import CoreLike.Syntax

type Env = M.Map Var Term

data StackFrame
  = Apply Var
  | Scrutinise [(AltCon, Term)]
  | PrimApply PrimOp [Value] [Term]
  | Update Var
  deriving (Show, Generic, Binary)

type Stack = [StackFrame]

type State = (Term, Env, Stack)

-- Note [Pushing new variables to the environment]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We need to rename every variable before pushing them to the environment and
-- of course update the code that uses those variables accordingly. Otherwise we
-- end up with overriding existing variables. Example:
--
--   let x = ...
--    in (\x -> ...) y
--
-- After the application updated `x` will be in the environment.
--
-- This also means that we should occasionally run garbage collection to remove
-- unused bindings from the environment. (not strictly necessary, but not doing
-- this makes debugging harder)

-- TODO: Rename 'Env' with 'Heap'.
-- TODO: Ideally 'Heap' should be kept abstract here, we don't want to use
--       M.insert accidentally and ruin everything.
-- TODO: Document why we need to pass stack to add new bindings.

envVars :: Env -> S.Set Var
envVars = M.keysSet

updateVars :: Stack -> S.Set Var
updateVars s = S.fromList [ v | Update v <- s ]

envVals :: Env -> [Var] -> [(Var, Term)]
envVals e vs = mapMaybe (\v -> (v,) <$> M.lookup v e) vs

-- NOTE: This updates RHSs of let bindings.
mapVars :: [(Var, Term)] -> Env -> Stack -> Term -> (Env, Term)
mapVars binds env stack body = (env', body')
  where
    freshs    = freshVarsForPfx "l_"
                  (S.unions [envVars env, S.fromList (map fst binds),
                             vars body, updateVars stack])
    renamings = zip (map fst binds) (map Var freshs)
    body'     = substTerms renamings body
    binds'    = zipWith (\l (_, r) -> (l, substTerms renamings r)) freshs binds
    env'      = foldl' (\e (v, t) -> M.insert v t e) env binds'

-- NOTE: Doesn't update value of new variable.
insertVar :: Var -> Term -> Env -> Stack -> Term -> (Env, Term)
insertVar v t env stack body = (env', body')
  where
    fresh = head $ freshVarsFor (S.insert v $ envVars env `S.union` updateVars stack)
    env'  = M.insert fresh t env
    body' = substTerm v (Var fresh) body

evalStep :: State -> Maybe State
evalStep (Var v, env, stack) = (, M.delete v env, Update v : stack) <$> M.lookup v env
evalStep (Value v, env, stack) = unwind v env stack
evalStep (App t v, env, stack) = Just (t, env, Apply v : stack)
evalStep (PrimOp op (arg1 : args), env, stack) =
    Just (arg1, env, PrimApply op [] args : stack)
evalStep (PrimOp op [], _, _) = error $ "evalStep: PrimOp without arguments: " ++ show op
evalStep (Case scr cases, env, stack) = Just (scr, env, Scrutinise cases : stack)
evalStep (LetRec binds rhs, env, stack) =
    let (env', rhs') = mapVars binds env stack rhs in Just (rhs', env', stack)

unwind :: Value -> Env -> Stack -> Maybe State
unwind _ _ [] = Nothing
unwind val env (Update var : stack) =
    -- it's OK to just update the env here
    Just (Value val, M.insert var (Value val) env, stack)
unwind (Lambda arg body) env (Apply v : stack) =
    let (env', body') = insertVar arg (Var v) env stack body in Just (body', env', stack)
-- TODO: not sure about this case (same thing also exists in symbolic evaluator)
unwind (Data con as) env (Apply v : stack) = Just (Value $ Data con (as ++ [v]), env, stack)
unwind v@(Data con args) env (Scrutinise cases : stack) = findCase cases
  where
    findCase :: [(AltCon, Term)] -> Maybe State
    findCase [] = Nothing
    findCase ((DataAlt con' args', rhs) : rest)
      | con == con' =
          let (env', rhs') = mapVars (zip args' (map Var args)) env stack rhs
           in Just (rhs', env', stack)
      | otherwise   = findCase rest
    findCase ((LiteralAlt{}, _) : rest) = findCase rest
    findCase ((DefaultAlt Nothing, rhs) : _) = Just (rhs, env, stack)
    findCase ((DefaultAlt (Just d), rhs) : _) =
      let (env', rhs') = insertVar d (Value v) env stack rhs in Just (rhs', env', stack)
unwind v@(Literal lit) env (Scrutinise cases : stack) = findCase cases
  where
    findCase :: [(AltCon, Term)] -> Maybe State
    findCase [] = Nothing
    findCase ((DataAlt{}, _) : rest) = findCase rest
    findCase ((LiteralAlt lit', rhs) : rest)
      | lit == lit' = Just (rhs, env, stack)
      | otherwise   = findCase rest
    findCase ((DefaultAlt Nothing, rhs) : _) = Just (rhs, env, stack)
    findCase ((DefaultAlt (Just d), rhs) : _) =
      let (env', rhs') = insertVar d (Value v) env stack rhs in Just (rhs', env', stack)
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
applyPrimOp Sub [Literal (Int i1), Literal (Int i2)] =
    Literal $ Int $ i1 - i2
applyPrimOp Mul [Literal (Int i1), Literal (Int i2)] =
    Literal $ Int $ i1 * i2
applyPrimOp Div [Literal (Int i1), Literal (Int i2)] =
    Literal $ Int $ i1 `div` i2
applyPrimOp Mod [Literal (Int i1), Literal (Int i2)] =
    Literal $ Int $ i1 `mod` i2
applyPrimOp Eq [Literal (Int i1), Literal (Int i2)] =
    Data (if i1 == i2 then "True" else "False") []
applyPrimOp op lits = error $ "Unhandled PrimOp " ++ show op ++ " args: " ++ show lits

-- | A "big-step" evaluator that takes steps until it's stuck. Returns new state
-- and a list of heap bindings that are updated during the evaluation.
--
-- Returns `Nothing` if it can't take any steps. (to save a `==` call)
--
-- NOTE: Doesn't effect the correctness because we use a set, but each variable
-- is added to the set multiple times. Example:
--
--   let x = ... in x
--
-- We see `Update x` frame first time when it's pushed to the stack and `x` is
-- replaced with RHS. We see it second time when RHS is evaluated to a value.
--
-- If it gets stuck on the way, then we see `Update x` once.
--
eval :: State -> Maybe (State, S.Set Var)
eval s@(_, _, Update v : _) =
    case evalStep s of
      Nothing -> Nothing
      Just s' ->
        case eval s' of
          Nothing        -> Just (s', S.singleton v)
          Just (s'', vs) -> Just (s'', S.insert v vs)
eval s = evalStep s >>= eval

-----------------------
-- * Garbage collection

gc :: Term -> Env -> Stack -> Env
gc root env stack =
    closure (M.fromList (mapMaybe lookupKV $ S.toList used))
  where
    used_stack = S.unions $ flip map stack $ \case
      Apply v           -> S.singleton v
      Scrutinise cases  -> S.unions $ map fvsCase cases
      PrimApply _ vs ts -> S.unions $ map fvsVal vs ++ map fvsTerm ts
      Update v          -> S.singleton v

    used_term = fvsTerm root

    used = S.union used_term used_stack

    closure_iter e =
      let vs = S.unions $ map (fvsTerm . snd) (M.toList e)
       in e `M.union` M.fromList (mapMaybe lookupKV (S.toList vs))

    closure e =
      let c = closure_iter e
       in if M.size e == M.size c then c else closure c

    lookupKV k = (k,) <$> M.lookup k env

-----------------------------
-- * Residual code generation

residualize :: State -> Term
residualize (term, env, []) = LetRec (M.toList env) term
residualize (term, env, Apply v : stack) = residualize (App term v, env, stack)
residualize (term, env, Scrutinise cases : stack) =
    residualize (Case term cases, env, stack)
residualize (term, env, PrimApply op vs ts : stack) =
    residualize (PrimOp op (map Value vs ++ term : ts), env, stack)
residualize (term, env, Update v : stack) =
    residualize (Var v, M.insert v term env, stack)

-----------------------------------------------
-- * Splitting the state for evaluating further

-- | Splitting is only possible when evaluation is stuck or completed(WHNF).
-- In other cases or if splitting is not possible for some reason, it returns
-- `Nothing`.
split :: State -> Maybe ([State], [(State, S.Set Var)] -> State)

-- Cases for completed evaluation:

split (v@(Value (Data _ args)), heap, stack) =
    let states =
          flip map args $ \arg -> (Var arg, M.delete arg heap, [])
        combine ss = (v, , stack) $
          -- We need to combine all these states into single state that'll
          -- represent progressed version of our initial state.
          --
          -- New states have to be in one of these conditions:
          -- 1. Stuck with an unbound name in focus
          -- 2. Stuck with empty continuation stack.
          --    (which means evaluation succeeded)
          -- 3. Non-exhaustive pattern matching.
          --    (TODO: To keep things simple maybe we should ignore this case and
          --     fail with `error` instead)
          --
          -- Because the evaluator gets stuck only when one of these happen.
          foldl' (\h (updatedVar, s) ->
                   case s of
                     -- Case (1). TODO: What to do with the stack here?
                     ((t@Var{}, h', stack'), updates) ->
                        M.insert updatedVar t $
                          M.union (M.fromList (envVals h' $ S.toList updates)) h

                     -- Case (2), we can just update the heap binding with this
                     -- new term.
                     ((t, h', []), updates) ->
                       M.insert updatedVar t $
                         M.union (M.fromList (envVals h' $ S.toList updates)) h

                     -- Case (3) is not handled.
                     _ -> error $ "Unhandled case in state combiner: " ++ show s)
                 heap (zip args ss)
    in Just (states, combine)

-- TODO: Complete this (function bodies etc.)
split (Value{}, _, _) = Nothing

-- Cases for getting stuck:

split (Var{}, _, _) = Nothing -- TODO: Can we make any progress here?


-- Other cases: (TODO: maybe report a bug here?)
split _ = Nothing

----------
-- Testing

initState :: FilePath -> IO (Either String State)
initState path =
    fmap ((Value $ Data "()" [], , []) . M.fromList) <$> parseFile path

setTerm :: String -> State -> (Either String State)
setTerm termStr (_, env, stack) = (, env, stack) <$> parseTerm termStr
