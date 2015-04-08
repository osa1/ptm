-- | Transform Core syntax back to haskell-src-exts syntax to be able to pretty
-- print.
module CoreLike.ToHSE where

import qualified Language.Haskell.Exts as HSE

import CoreLike.Syntax

hseModule :: [(Var, Term)] -> HSE.Module
hseModule decls =
    HSE.Module dummyLoc (HSE.ModuleName "main") [] Nothing Nothing [] $ map bindToHSE decls

termToHSE :: Term -> HSE.Exp
termToHSE (Var v) =
    -- FIXME: This variable may contain dots, maybe take that into account
    HSE.Var (HSE.UnQual (HSE.Ident v))
termToHSE (Value v) = valueToHSE v
termToHSE (App term var) =
    -- TODO: Merge nested applications.
    -- TODO: Inline variable if it's used once.
    HSE.App (termToHSE term) (HSE.Var (HSE.UnQual (HSE.Ident var)))
termToHSE (Case scr cases) =
    HSE.Case (termToHSE scr) (map altToHSE cases)
termToHSE (LetRec binds rhs) =
    HSE.Let (HSE.BDecls $ map bindToHSE binds) (termToHSE rhs)

valueToHSE :: Value -> HSE.Exp
valueToHSE (Lambda var rhs) =
    -- FIXME: use some dummy value for locs
    -- TODO: Merge nested lambdas
    HSE.Lambda dummyLoc [HSE.PVar (HSE.Ident var)] (termToHSE rhs)
valueToHSE (Data con args) =
    -- FIXME: Handle special symbols
    foldr (\arg f -> HSE.App f (HSE.Var (HSE.UnQual (HSE.Ident arg))))
          (HSE.Con (HSE.UnQual (HSE.Ident con))) args
valueToHSE (Literal (Int i)) = HSE.Lit (HSE.Int i)
valueToHSE (Literal (Char c)) = HSE.Lit (HSE.Char c)
valueToHSE ind@Indirect{} = error $ "Can't translate Indirects to HSE: " ++ show ind

altToHSE :: (AltCon, Term) -> HSE.Alt
altToHSE (con, t) =
    HSE.Alt dummyLoc (altConToHSE con) (HSE.UnGuardedRhs $ termToHSE t) (HSE.BDecls [])

altConToHSE :: AltCon -> HSE.Pat
altConToHSE (DataAlt con args) =
    HSE.PApp (HSE.UnQual $ HSE.Ident con) (map (HSE.PVar . HSE.Ident) args)
altConToHSE (LiteralAlt lit) = HSE.PLit HSE.Signless $ litToHSE lit
altConToHSE (DefaultAlt Nothing) = HSE.PWildCard
altConToHSE (DefaultAlt (Just v)) = HSE.PVar (HSE.Ident v)

bindToHSE :: (Var, Term) -> HSE.Decl
bindToHSE (v, t) =
    HSE.FunBind [HSE.Match dummyLoc (HSE.Ident "")
                   [HSE.PVar (HSE.Ident v)]
                   Nothing
                   (HSE.UnGuardedRhs $ termToHSE t)
                   (HSE.BDecls [])]

litToHSE :: Literal -> HSE.Literal
litToHSE (Int i) = HSE.Int i
litToHSE (Char c) = HSE.Char c

dummyLoc :: HSE.SrcLoc
dummyLoc = HSE.SrcLoc "" 0 0
