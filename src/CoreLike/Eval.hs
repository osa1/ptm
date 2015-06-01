{-# LANGUAGE DeriveAnyClass, DeriveGeneric, LambdaCase, TupleSections #-}

module CoreLike.Eval where

import Control.Arrow (second)
import Data.Binary (Binary)
import Data.List (foldl')
import Data.List ((\\))
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Set as S
import GHC.Generics (Generic)
import qualified Language.Haskell.Exts as HSE
import qualified Text.PrettyPrint.Leijen as PP

import CoreLike.Parser
import CoreLike.Simplify
import CoreLike.Syntax
import CoreLike.ToHSE

import Debug.Trace

data StackFrame
  = Apply Var
  | Scrutinise [(AltCon, Term)]
  | PrimApply PrimOp [Value] [Term]
  | Update Var
  deriving (Show, Eq, Generic, Binary)

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

-- | Unwind the whole stack. Focus may not be a value.
unwindAll :: State -> (Term, Env)
unwindAll (t, e, []) = (t, e)
unwindAll (Value v, e, s@(f : fs)) =
    case unwind v e s of
      Just st -> unwindAll st
      Nothing ->
        case f of
          Apply arg -> unwindAll (App (Value v) arg, e, fs)
          Scrutinise cases -> unwindAll (Case (Value v) cases, e, fs)
          PrimApply op vs ts ->
            unwindAll (PrimOp op $ (map Value $ vs ++ [v]) ++ ts, e, fs)
          Update var -> unwindAll (Value v, M.insert var (Value v) e, fs)
unwindAll (t, e, Apply v : fs) = unwindAll (App t v, e, fs)
unwindAll (t, e, Scrutinise cases : fs) = unwindAll (Case t cases, e, fs)
unwindAll (t, e, PrimApply op vs ts : fs) =
    unwindAll (PrimOp op $ map Value vs ++ ts ++ [t], e, fs)
unwindAll (t, e, Update v : fs) =
    -- TODO: This looks dangerous -- may duplicate lots of work.
    unwindAll (t, M.insert v t e, fs)

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
        Just $ case eval s' of
                 Nothing        -> (s', S.singleton v)
                 Just (s'', vs) -> (s'', S.insert v vs)
eval s = do
    s' <- evalStep s
    return $ fromMaybe (s', S.empty) $ eval s'

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

-- | Remove indirections from the heap.
--
-- E.g. if we have
--
--   l_1 = l_2
--   l_2 = l_3
--
-- It changes l_1 to l_1 = l_3
--
-- NOTE: May lead to unused bindings, so it may be a good idea to call `gc`
-- after this.
--
-- TODO: We can probably do some transformations like unboxing, by inlining
-- literals.
simplHeap :: Env -> Env
simplHeap env = M.map removeLinks env
  where
    removeLinks :: Term -> Term
    removeLinks (Var v) = Var $ removeLinks' v
    removeLinks (App f v) = App (removeLinks f) (removeLinks' v)
    removeLinks t = t -- FIXME: We can improve this a lot

    removeLinks' :: Var -> Var
    removeLinks' v =
      case M.lookup v env of
        Just (Var v') -> removeLinks' v'
        _             -> v

-----------------------------
-- * Residual code generation

residualize :: State -> Term
residualize (term, env, []) = simpl $ LetRec (M.toList env) term
residualize (term, env, Apply v : stack) = residualize (App term v, env, stack)
residualize (term, env, Scrutinise cases : stack) =
    residualize (Case term cases, env, stack)
residualize (term, env, PrimApply op vs ts : stack) =
    residualize (PrimOp op (map Value vs ++ term : ts), env, stack)
residualize (term, env, Update v : stack) =
    residualize (Var v, M.insert v term env, stack)

-----------------------------------------------
-- * Splitting the state for evaluating further

zipErr :: [a] -> [b] -> [(a, b)]
zipErr (a : as) (b : bs) = (a, b) : zipErr as bs
zipErr []       []       = []
zipErr _        _        = error "zipErr: lengths are not equal"

-- | evaluate -> split -> recurse
evalSplit :: Int -> State -> State
evalSplit n s = splitEval n $ maybe s fst $ eval s

-- | split -> evaluate -> recurse
splitEval :: Int -> State -> State
splitEval 0 s = s
splitEval n (v@(Value (Data _ args)), env, stack) =
  let states = flip map args $ \arg -> (arg, (Var arg, , []))
   in (v, , stack) $ foldl' (\e (a, s) ->
         let (t, e', s') = evalSplit (n - 1) (s e)
             (t', e'')   = unwindAll (t, e', s')
          in M.insert a t' e'') env states
splitEval n (Var v, env, Scrutinise cases : fs) =
  let states = flip map cases $ \(con, rhs) ->
        case con of
          DataAlt dCon vs     ->
            let v_fresh = head $ freshVarsInTerm rhs \\ [v] in
            (substTerm v (Var v_fresh) rhs, M.insert v_fresh (Value $ Data dCon vs) env, [])
          LiteralAlt lit      -> (rhs, M.insert v (Value $ Literal lit) env, [])
          DefaultAlt (Just d) -> (rhs, M.insert d (Var v) env, [])
   in (Var v, env,
       Scrutinise
         (zipWith (\c s -> (c,   residualize
                               . filterEnvUnchanged env
                               . uncurry (,,[])
                               . unwindAll
                               . evalSplit (n - 1)
                               $ s))
                  (map fst cases) states) : fs)
splitEval n (Var v, env, Update v' : fs) = splitEval n (Var v, M.insert v' (Var v) env, fs)
splitEval _ s = s -- TODO: Implement this

filterEnvUnchanged :: Env -> State -> State
filterEnvUnchanged e0 (t, e, s) = (t, M.filterWithKey f e, s)
  where
    f :: Var -> Term -> Bool
    f v t = case M.lookup v e0 of
              Nothing -> True
              Just t' -> t /= t'

-- | Splitting is only possible when evaluation is stuck or completed(WHNF).
-- In other cases or if splitting is not possible for some reason, it returns
-- `Nothing`.
split :: State -> Maybe ([State], [(State, S.Set Var)] -> State)

-- Cases for completed evaluation:

split (v@(Value (Data _ args)), env, stack) =
    let states =
          flip map args $ \arg -> (Var arg, env, [])
        combine ss = (v, , stack) $
          trace ("combining states: " ++ showStates (map fst ss)) $
          foldl' combineFold env (zipErr args ss)
    in Just (states, combine)

-- TODO: Complete this (function bodies etc.)
split (Value{}, _, _) = Nothing

-- Cases for getting stuck:

split (v@Var{}, env, (Apply arg : stack)) =
    let states = [ (Var arg, env, []) ]
        combine ss = (v, , stack) $
          trace ("combining states: " ++ showStates (map fst ss)) $
          foldl' combineFold env (zipErr [arg] ss)
    in Just (states, combine)

split (Var{}, _, _) = Nothing -- TODO: add other cases here

-- Other cases: (TODO: maybe report a bug here?)
split _ = Nothing

-- We need to combine all these states into single state that'll represent
-- progressed version of our initial state.
--
-- New states have to be in one of these conditions:
-- 1. Stuck with an unbound name in focus
-- 2. Stuck with empty continuation stack.
--    (which means evaluation succeeded)
-- 3. Non-exhaustive pattern matching.
--    (TODO: To keep things simple maybe we should ignore this case and fail
--     with `error` instead)
--
-- Because the evaluator gets stuck only when one of these happen.
combineFold
  :: Env
     -- ^ partially updated environment
  -> (Var, (State, S.Set Var))
     -- ^ (the variable we're updating,
     --    (state after the update,
     --     other variables that are updated while
     --     evaluating the first element of tuple))
  -> Env
     -- ^ environment after updating old environment for the evaluated bindings

-- Case (1). TODO: What to do with the stack here?
combineFold h (updatedVar, ((t@Var{}, h', stack'), updates)) =
  trace ("M.insert (1) " ++ updatedVar ++ " " ++ show t) $
  trace ("Updates: " ++ show updates) $
  M.insert updatedVar (residualize (t, M.empty, stack')) $
    M.union (M.fromList (envVals h' $ S.toList updates)) h

-- Case (2), we can just update the heap binding with this new term.
combineFold h (updatedVar, ((t, h', []), updates)) =
  trace ("M.insert (2) " ++ updatedVar ++ " " ++ show t) $
  M.insert updatedVar t $
    M.union (M.fromList (envVals h' $ S.toList updates)) h

-- Case (3) is not handled.
combineFold _ (_, (s, _)) =
  error $ "Unhandled case in state combiner: " ++ show s

--------------------------------------
-- | Main routine for supercompilation

drive :: State -> State
drive = evalSplit 3 -- FIXME: limit splits to 10 for now

-----------------------------------
-- * Testing and utilities for REPL

initState :: FilePath -> IO (Either String State)
initState path =
    fmap ((Value $ Data "()" [], , []) . M.fromList) <$> parseFile path

setTerm :: String -> State -> (Either String State)
setTerm termStr (_, env, stack) = (, env, stack) <$> parseTerm termStr

initState' :: FilePath -> String -> IO State
initState' path termStr = do
    st <- either error id <$> initState path
    return $ either error id $ setTerm termStr st

---------------------------
-- * Pretty-printing states

ppTerm :: Term -> PP.Doc
ppTerm = PP.string . HSE.prettyPrint . termToHSE

ppEnv :: Env -> PP.Doc
ppEnv =
    PP.list
    . map (\(k, v) -> PP.nest 4 (PP.text k PP.<+> PP.text "=" PP.</>
                                   PP.string (HSE.prettyPrint (termToHSE v))))
    . M.toList

ppStack :: Stack -> PP.Doc
ppStack = PP.list . map ppStackFrame . reverse

-- haskell-src-exts doesn't export methods for generating `Doc`, and even if it
-- did we couldn't incorporate it easily since it's using `pretty`. So we just
-- pretty-print terms, wrap them with `PP.string` and hope that `wl-pprint`
-- won't remove newlines.
ppStackFrame :: StackFrame -> PP.Doc
ppStackFrame = PP.string . HSE.prettyPrint . termToHSE . ppF
  where
    ppF (Apply v) = App (Var "●") v
    ppF (Scrutinise cases) = Case (Var "●") cases
    ppF (PrimApply op vs ts) = PrimOp op (map Value vs ++ ts)
    ppF (Update v) = Value $ Data "Update" [v]

ppState :: State -> PP.Doc
ppState (t, e, s) = PP.tupled [ ppEnv e, ppStack s, ppTerm t ]

ppStates :: [State] -> PP.Doc
ppStates = PP.list . map ppState

showDoc :: PP.Doc -> String
showDoc = flip PP.displayS "" . PP.renderPretty 0.8 100

showState :: State -> String
showState = showDoc . ppState

showStates :: [State] -> String
showStates = showDoc . ppStates
