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
     in if null binds'' then rhs else LetRec binds'' rhs
