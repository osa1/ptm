module CoreLike.Simplify (simpl) where

import Control.Arrow (second)
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
simpl :: Term -> Term
simpl t@Var{}            = t
simpl t@Value{}          = t
simpl (App f args)       = App (simpl f) args
simpl (PrimOp op args)   = PrimOp op (map simpl args)
simpl (Case scrt alts)   = Case (simpl scrt) (map (second simpl) alts)
simpl (LetRec binds rhs) =
    let binds'  = map (second simpl) binds
        fvs     = S.unions $ fvsTerm rhs : map (fvsTerm . snd) binds'
        binds'' = filter ((`S.member` fvs) . fst) binds'
     in case simpl rhs of
          r@(LetRec tbs rhs') ->
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
            if null (binds'' ++ tbs)
               then rhs'
               else
                 let
                   renamings :: [(Var, Var)]
                   renamings =
                     zip (intersect
                           -- We use compare free variables in first bindings,
                           -- because after merging letrecs those may be bound
                           -- by nested letrec (e.g. variable capturing).
                           (S.toList (snd (fvsBindings binds'')))
                           (map fst tbs))
                         (freshVarsInTerm r)

                   renamings' :: [(Var, Term)]
                   renamings' = map (second Var) renamings
                 in
                   simplBinds
                     (binds'' ++ renameWBinders tbs renamings)
                     (substTerms renamings' rhs')
          rhs' ->
            if null binds'' then rhs' else simplBinds binds'' rhs'

simplBinds :: [(Var, Term)] -> Term -> Term
simplBinds bs rhs =
    let varBs = collectVarBs bs
        bs'   = removeBs (map fst varBs) bs
     in substTerms varBs $ if null bs' then rhs else LetRec bs' rhs
  where
    collectVarBs :: [(Var, Term)] -> [(Var, Term)]
    collectVarBs []                    = []
    collectVarBs (b@(_, Var _) : rest) = b : collectVarBs rest
    collectVarBs (_            : rest) = collectVarBs rest

    removeBs :: [Var] -> [(Var, Term)] -> [(Var, Term)]
    removeBs vs = filter (\(v, _) -> not (v `elem` vs))
