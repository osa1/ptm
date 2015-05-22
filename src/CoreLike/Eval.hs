{-# LANGUAGE TupleSections, TupleSections #-}

module CoreLike.Eval where

import Data.List (foldl')
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import CoreLike.Syntax
import CoreLike.Parser -- testing

type Env = M.Map Var Term

data StackFrame
  = Apply Var
  | Scrutinise [(AltCon, Term)]
  | PrimApply PrimOp [Value] [Term]
  | Update Var
  deriving (Show)

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

----------
-- Testing

initState :: FilePath -> IO (Either String State)
initState path =
    fmap ((Value $ Data "()" [], , []) . M.fromList) <$> parseFile path

setTerm :: String -> State -> (Either String State)
setTerm termStr (_, env, stack) = (, env, stack) <$> parseTerm termStr
