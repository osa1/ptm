module CoreLike.Simplify (simpl) where

import Data.Bifunctor (second)
import Data.List (intersect)
import qualified Data.Set as S

import CoreLike.Syntax

-- | Run a simplification pass:
--
--   * Remove unused let bindings.
--   * Flatten nested let bindings. (sometimes requires renaming binders)
--   * Substitute let bindings in form `a = b` where b is a variable.
--
-- (That's all we do for now)
--
-- FIXME: This should be an optional step.. `step` by itself should reduce terms
-- as much as possible, but currently `step` gets stuck if we don't use `simpl`.
-- One example is `let _ = _ in 1`, `step` doesn't reduce this to `1`.
--
-- FIXME: I disabled most of the stuff, until I decide which ones are really
-- necessary here.
--
simpl :: Term ann -> Term ann
simpl t@Var{} = t
simpl t@PrimOp{} = t
simpl (Value ann val) = Value ann $ simplValue val
simpl (App ann t1 t2) = App ann (simpl t1) (simpl t2)
simpl (Case ann scrt alts) = Case ann (simpl scrt) (map (second simpl) alts)
simpl (LetRec ann bndrs body) =
    LetRec ann (filter ((`S.member` all_fvs) . fst) bndrs') (simpl body)
  where
    bndrs' = map (second simpl) bndrs
    body_fvs = fvsTerm body
    bndrs_fvs = map (fvsTerm . snd) bndrs'
    all_fvs = S.unions (body_fvs : bndrs_fvs)

simplValue :: Value ann -> Value ann
simplValue (Lambda ann b t)  = Lambda ann b $ simpl t
simplValue (Data ann con ts) = Data ann con $ map simpl ts
simplValue v@Literal{}       = v

{-
-- Case-case transformation. We add this as a simplification pass since that's
-- not really an operational semantics step.
--
-- FIXME: This is broken. Example test case:
--
--   case (case _ of { [] -> e1; x : xs -> e2 }) of
--     [] -> e3
--     y : ys -> .. x .. xs ..
--
-- Will be transformed to:
--
--   case _ of
--      [] ->
--        case e1 of
--          [] -> e3
--          y : ys -> .. x .. xs ..
--      x : xs ->
--        case e2 of
--          [] -> e3
--          y : ys -> .. x .. xs ..
-- captured variables:   ^    ^^
simpl (Case (Case scrt alts1) alts2) =
    simpl $ Case scrt (map (\(p, rhs) -> (p, Case rhs alts2)) alts1)
simpl (Case scrt alts)   = Case (simpl scrt) (map (second simpl) alts)
simpl (LetRec binds rhs0) =
    case simpl rhs0 of
      r@(LetRec tbs rhs')
        -- We should be careful with renamings here. Example:
        --
        --   let y = .. in
        --    let x = .. y .. in
        --     let y = .. in
        --      ..
        --
        -- Flattened version of this is not even valid, because it binds y
        -- twice. Another example:
        --
        --   let y = .. x .. in
        --    let  x = .. y .. in
        --      ..
        --
        -- Here binder of first x is not known. If we flatten this without
        -- renaming second x, first x will be bound by it.
        | null (binds'' ++ tbs) -> rhs'
        | otherwise             ->
          let
            renamings :: [(Var, Var)]
            renamings =
              zip (intersect
                    -- We use compare free variables in first bindings, because
                    -- after merging letrecs those may be bound by nested letrec
                    -- (e.g. variable capturing).
                    (S.toList (snd (fvsBindings binds'')))
                    (map fst tbs))
                  (freshVarsInTerm r)

            renamings' :: [(Var, Term)]
            renamings' = map (second Var) renamings

            -- second step, we rename binders in nested let that are also
            -- binders in outer let
            mergeLets :: [(Var, Term)] -> [(Var, Term)] -> Term
                      -> ([(Var, Term)], Term)
            mergeLets bs1 bs2 rhs =
              let
                rs = zip (intersect (map fst bs1) (map fst bs2))
                         -- TODO: fix this ugly hack
                         (freshVarsInTerm (LetRec (bs1 ++ bs2)
                                                  (Value (Literal undefined))))
                rs' = map (second Var) rs
              in
                (bs1 ++ renameWBinders bs2 rs, substTerms rs' rhs)
          in
            uncurry simplBinds
              (mergeLets binds'' (renameWBinders tbs renamings)
                         (substTerms renamings' rhs'))
      rhs' ->
        if null binds'' then rhs' else simplBinds binds'' rhs'
  where
    closure_iter, closure :: S.Set Var -> S.Set Var
    closure_iter vs = S.unions . (vs :) $
                        map (fvsTerm . snd) $ filter ((`S.member` vs) . fst) binds

    closure vs =
      let c = closure_iter vs
       in if S.size vs == S.size c then vs else closure c

    binds'  = map (second simpl) binds
    fvs     = closure (fvsTerm rhs0)
    binds'' = filter ((`S.member` fvs) . fst) binds'

-- | Remove bindings in form `a = b` where b is a variable by inlining.
simplBinds :: [(Var, Term)] -> Term -> Term
simplBinds bs rhs =
    -- We need to be careful with the substitution here. if we do this:
    --
    --   substTerms varBs (LetRec bs' rhs)
    --
    -- It may try to rename some of the binders to avoid variable capturing,
    -- but renaming is exactly what we should avoid here. Example:
    --
    --   let v25 = (:) v1 nil
    --       v22 = v25
    --    in (:) v0 v22
    --
    -- We try to do [v25\v22], but `v25` is a open term and `v25` is free in
    -- it. So it renames `let v25 = ...` part.
    if null bs' then substTerms varBs rhs
                else LetRec (map (second $ substTerms varBs) bs') (substTerms varBs rhs)
  where
    varBs = collectVarBs bs
    bs'   = removeBs (map fst varBs) bs

    collectVarBs :: [(Var, Term)] -> [(Var, Term)]
    collectVarBs []                    = []
    collectVarBs (b@(_, Var _) : rest) = b : collectVarBs rest
    collectVarBs (_            : rest) = collectVarBs rest

    removeBs :: [Var] -> [(Var, Term)] -> [(Var, Term)]
    removeBs vs = filter (\(v, _) -> not (v `elem` vs))
-}
