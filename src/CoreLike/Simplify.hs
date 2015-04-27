module CoreLike.Simplify where

import qualified Data.Set as S
import Control.Arrow (second)

import CoreLike.Syntax

-- | Run a simplification pass:
--
--   * Remove unused let bindings.
--
-- (That's all we do for now)
--
-- FIXME: This should be an optinal step.. `step` by itself should reduce terms
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
          LetRec tbs rhs' ->
            if null (binds'' ++ tbs) then rhs' else LetRec (binds'' ++ tbs) rhs'
          rhs' ->
            if null binds'' then rhs' else LetRec binds'' rhs'
