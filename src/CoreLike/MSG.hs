{-# LANGUAGE ScopedTypeVariables #-}

-- | Most specific generalization of terms.
module CoreLike.MSG where

import CoreLike.Parser (parseTerm')
import CoreLike.Syntax

import qualified Data.Map.Strict as M
import qualified Data.Set as S

--------------------------------------------------------------------------------

-- Non-capturing substitution: A substitution that doesn't make a free variable
-- bound.
--
-- If we want to generate non-capturing substitutions, we need to pass bound
-- variables to `msg`.

type Subst ann = M.Map Var (Term ann)

type Subst' = Subst ()

emptySubsts :: Subst ann
emptySubsts = M.empty

lookupSubstRhs :: Var -> Subst ann -> S.Set Var
lookupSubstRhs v0 = M.foldlWithKey' f S.empty
  where
    f :: S.Set Var -> Var -> Term ann -> S.Set Var
    f acc k (Var _ v)
      | v == v0   = S.insert k acc
      | otherwise = acc
    f acc _ _ = acc

applySubsts :: Subst ann -> Term ann -> Term ann
applySubsts s t = substTerms (M.toList s) t

--------------------------------------------------------------------------------

-- | Rigids variables are variables we should avoid generating. It's basically a
-- set of bound variables in our MSG term.
type Rigids = S.Set Var

emptyRigids :: Rigids
emptyRigids = S.empty

isRigid :: Var -> Rigids -> Bool
isRigid = S.member

--------------------------------------------------------------------------------

msg' :: Term ann -> Term ann -> Maybe (Subst ann, Term ann, Subst ann)
msg' t1 t2 =
    -- We initialize rigids as free variables, because we don't want to
    -- accidentally capture variables and most of the time(only exception I can
    -- think of is tests) arguments should be closed terms. If they're not, we
    -- just assume they're sub-terms of a closed term, so free variables should
    -- be bound in some context.
    msg t1 emptySubsts t2 emptySubsts (fvsTerm t1 `S.union` fvsTerm t2)

-- | For testing in REPL
msgStr :: String -> String -> Maybe (Subst', Term', Subst')
msgStr t1 t2 = msg' (parseTerm' t1) (parseTerm' t2)

-- Currently we use tags first(left) term. We may want to experiment with this.

foldMsgs :: [Term ann] -> Subst ann -> [Term ann] -> Subst ann -> Rigids
         -> Maybe (Subst ann, [Term ann], Subst ann)

foldMsgs [] sl [] sr _ = return (sl, [], sr)

foldMsgs (t_l : ts_l) sl (t_r : ts_r) sr rs = do
    (sl' , t , sr' ) <- msg t_l sl t_r sr rs
    (sl'', ts, sr'') <- foldMsgs ts_l sl' ts_r sr' rs
    return (sl'', t : ts, sr'')

foldMsgs _ _ _ _ _ = error "foldMsgs: arguments with different number of terms"

msg :: forall ann .
       Term ann -> Subst ann -> Term ann -> Subst ann -> Rigids
    -> Maybe (Subst ann, Term ann, Subst ann)

msg (Var al vl) sl (Var ar vr) sr rs = do
    (sl', v, sr') <- msgVar vl al sl vr ar sr rs
    return (sl', Var al v, sr')

msg (PrimOp al opl ts_l) sl (PrimOp _ opr ts_r) sr rs
  | opl /= opr || length ts_l /= length ts_r
  = error $ "msg of two primop applications with different primops and/or arity, "
            ++ "I don't think this should be possible"
  | otherwise
  = do (sl', ts, sr') <- foldMsgs ts_l sl ts_r sr rs
       return (sl', PrimOp al opl ts, sr')

msg (App al t1_l t2_l) sl (App _ t1_r t2_r) sr rs = do
    (sl',  t1, sr' ) <- msg t1_l sl  t1_r sr  rs
    (sl'', t2, sr'') <- msg t2_l sl' t2_r sr' rs
    return (sl'', App al t1 t2, sr'')

msg (Value al1 (Data al2 con1 ts_l)) sl (Value _ (Data _ con2 ts_r)) sr rs
  | con1 /= con2 || length ts_l /= length ts_r
  = error $ "msg of two constructors with different names and/or arity, "
            ++ "I don't think this should be possible"
  | otherwise
  = do (sl', ts, sr') <- foldMsgs ts_l sl ts_r sr rs
       return (sl', Value al1 (Data al2 con1 ts), sr')

msg vl@(Value al1 (Lambda al2 bl body_l)) sl vr@(Value ar1 (Lambda ar2 br body_r)) sr rs
  | bl == br
  = do (sl', body, sr') <- msg body_l sl body_r sr rs
       return (sl', Value al1 (Lambda al2 bl body), sr')
  | otherwise
  = do let
         -- create a fresh variable that is not in either one of the terms
         fv = freshIn (fvsTerm vl `S.intersection` fvsTerm vr)
         -- rename function bodies for this fresh variable
         body_l' = renameTerm bl fv body_l
         body_r' = renameTerm br fv body_r
         -- generate msg for these two terms with same binders
         rs' = S.insert bl $ S.insert br $ S.insert fv rs
       -- we don't need to rename things back, because fv is in rigids so msg
       --   1. msg can't map fv to things (because it generates non-capturing
       --      substitutions)
       --   2. it can't map things to fv, because we added fv is in rigids
       -- TODO: I'm a bit tired at the moment, make sure these are correct.
       msg (Value al1 (Lambda al2 fv body_l')) sl (Value ar1 (Lambda ar2 fv body_r')) sr rs'

msg (Case _ _ cases_l) _ (Case _ _ cases_r) _ _
  | not expected
  = error "msg: Case expressions have unexpected cases"
  where
    expected =
      length cases_l == length cases_r &&
        and (zipWith compareCaseBndrs (map fst cases_l) (map fst cases_r))

    compareCaseBndrs DefaultAlt{}       DefaultAlt{}       = True
    compareCaseBndrs (LiteralAlt l1)    (LiteralAlt l2)    = l1 == l2
    compareCaseBndrs (DataAlt con1 ts1) (DataAlt con2 ts2) =
      con1 == con2 && length ts1 == length ts2
    compareCaseBndrs _                  _                  = False

msg t1@(Case ann tl0 cases_l) sl0 t2@(Case _ tr0 cases_r) sr0 rs = do
    (sl, t, sr) <- msg tl0 sl0 tr0 sr0 rs
    let
      allVars  = vars t1 `S.intersection` vars t2
      -- `renameCaseBinders` will return cases with same binder names in
      -- corresponding cases because 1) we pass same `allVars`, so list of
      -- generated fresh variables will be the same 2) cases are sorted, and
      -- number of binders in patterns are the same 3) no binder is used
      -- multiple times in a pattern. (FIXME: (3) is not guaranteed for now)
      cases_l' = renameCaseBinders allVars cases_l
      cases_r' = renameCaseBinders allVars cases_r

    (sl', cases, sr') <- foldMsgCase cases_l' sl cases_r' sr
    return (sl', Case ann t cases, sr')
  where
    foldMsgCase :: [(AltCon, Term ann)] -> Subst ann
                -> [(AltCon, Term ann)] -> Subst ann
                -> Maybe (Subst ann, [(AltCon, Term ann)], Subst ann)
    foldMsgCase [] sl [] sr = return (sl, [], sr)
    foldMsgCase ((con, rhs_l) : csl) sl ((_, rhs_r) : csr) sr = do
      (sl',  rhs,  sr')  <- msg rhs_l sl rhs_r sr (altConVars con `S.intersection` rs)
      (sl'', rest, sr'') <- foldMsgCase csl sl' csr sr'
      return (sl'', (con, rhs) : rest, sr'')
    foldMsgCase _ _ _ _ = error "foldMsgCase: Different number of cases"

-- Here's how we handle LetRecs:
--
-- We make some simplifying assumptions, otherwise this problem is too hard to
-- solve. Assume that we have these two expressions:
--
--   let x = t1        let a = t3
--       y = t2            b = t4
--    in ...            in ...
--
-- There's no easy/good way to rename x, y, a, b in a way that 1) gives us a msg
-- if possible 2) not exponential as lets get nested.
--
-- But, we observe that often both expressions are coming from same code, like
-- in the case of recursive calls. This means that we can assume we have same
-- list of binders, if the assumption doesn't hold we just fail.
--
msg (LetRec _ bndrs_l _) _ (LetRec _ bndrs_r _) _ _
  | not expected
  = error "msg: Unexpected LetRecs"
  where
    expected = map fst bndrs_l == map fst bndrs_r

msg (LetRec ann bndrs_l body_l) sl (LetRec _ bndrs_r body_r) sr rs = do
    let bndrs = map fst bndrs_l
        rs'   = rs `S.intersection` S.fromList bndrs
    (sl', rhss, sr') <- foldMsgs (map snd bndrs_l) sl (map snd bndrs_r) sr rs'
    (sl'', body, sr'') <- msg body_l sl' body_r sr' rs'
    return (sl'', LetRec ann (zip bndrs rhss) body, sr'')

msg _ _ _ _ _ = Nothing

msgVar :: Var -> ann -> Subst ann -- left
       -> Var -> ann -> Subst ann -- right
       -> Rigids -> Maybe (Subst ann, Var, Subst ann)

msgVar vl _ sl vr _ sr rs
  | vl == vr && isRigid vl rs
  = Just (sl, vl, sr)

  | vl /= vr && (isRigid vl rs || isRigid vr rs)
  = Nothing

  | left_ss  <- lookupSubstRhs vl sl
  , right_ss <- lookupSubstRhs vr sr
  , let vs = S.intersection left_ss right_ss
  , (v : _)  <- S.toList vs
  = -- TODO: This case doesn't make sense, as in, I don't understand how can
    -- this happen. Should investigate this further later.
    Just (sl, v, sr)

msgVar vl al sl vr ar sr rs =
    Just (M.insert fv (Var al vl) sl, fv, M.insert fv (Var ar vr) sr)
  where
    fv = freshIn rs

--------------------------------------------------------------------------------

-- TODO: Generate variables with different prefix to be able to track
freshIn :: Rigids -> Var
freshIn = freshFor

renameCaseBinders :: S.Set Var -> [(AltCon, Term ann)] -> [(AltCon, Term ann)]
renameCaseBinders = map . renameCaseBinders'

renameCaseBinders' :: S.Set Var -> (AltCon, Term ann) -> (AltCon, Term ann)
renameCaseBinders' used (DataAlt con vs, rhs) =
    let con_rns = zip vs (freshVarsFor used)
     in (DataAlt con (map snd con_rns), renameTerms con_rns rhs)
renameCaseBinders' _ c@(LiteralAlt{}, _) = c
renameCaseBinders' _ c@(DefaultAlt Nothing, _) = c
renameCaseBinders' used (DefaultAlt (Just v), rhs) =
    let fresh = freshFor used
     in (DefaultAlt (Just fresh), renameTerm v fresh rhs)
