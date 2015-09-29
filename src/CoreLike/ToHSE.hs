-- | Transform Core syntax back to haskell-src-exts syntax to be able to pretty
-- print.
module CoreLike.ToHSE where

import Data.List (foldl')
import qualified Language.Haskell.Exts as HSE
import Prelude hiding (LT)

import CoreLike.Syntax

hseModule :: [(Var, Term ann)] -> HSE.Module
hseModule decls =
    HSE.Module dummyLoc (HSE.ModuleName "Main") [] Nothing Nothing [] $ map bindToHSE decls

termToHSE :: Term ann -> HSE.Exp

-- FIXME: Handle special symbols here
termToHSE (Var _ v) =
    -- FIXME: This variable may contain dots, maybe take that into account
    HSE.Var (HSE.UnQual (HSE.Ident v))

termToHSE (PrimOp _ op ts) =
    app (HSE.Var (HSE.UnQual (HSE.Symbol (primOpStr op)))) (map termToHSE ts)

termToHSE (Value _ v) = valueToHSE v
termToHSE (App _ t1 t2) = HSE.App (termToHSE t1) (termToHSE t2)
termToHSE (Case _ scr cases) =
    HSE.Case (termToHSE scr) (map altToHSE cases)
termToHSE (LetRec _ binds rhs) =
    HSE.Let (HSE.BDecls $ map bindToHSE binds) (termToHSE rhs)

valueToHSE :: Value ann -> HSE.Exp
valueToHSE (Lambda _ var rhs) =
    -- FIXME: use some dummy value for locs
    case termToHSE rhs of
      HSE.Lambda _ pats body -> HSE.Lambda dummyLoc (HSE.PVar (HSE.Ident var) : pats) body
      body -> HSE.Lambda dummyLoc [HSE.PVar (HSE.Ident var)] body
valueToHSE (Data _ con args) =
    -- FIXME: Handle special symbols
    foldl' (\f arg -> HSE.App f   (termToHSE arg))
           (HSE.Con (HSE.UnQual (HSE.Ident con))) args
valueToHSE (Literal _ (Int i)) = HSE.Lit (HSE.Int i)
valueToHSE (Literal _ (Char c)) = HSE.Lit (HSE.Char c)
-- valueToHSE ind@Indirect{} = error $ "Can't translate Indirects to HSE: " ++ show ind

-- primOpToHSE :: PrimOp -> [Term] -> HSE.Exp
-- primOpToHSE op [t1, t2] = HSE.InfixApp (termToHSE t1) (primOpToQOp op) (termToHSE t2)
-- primOpToHSE op args = error $ "Can't convert PrimOp to HSE: " ++ show op ++ ", " ++ show args

-- primOpToQOp :: PrimOp -> HSE.QOp
-- primOpToQOp = HSE.QVarOp . HSE.UnQual . HSE.Symbol . primOpStr

altToHSE :: (AltCon, Term ann) -> HSE.Alt
altToHSE (con, t) =
    HSE.Alt dummyLoc (altConToHSE con) (HSE.UnGuardedRhs $ termToHSE t) (HSE.BDecls [])

altConToHSE :: AltCon -> HSE.Pat

-- special cases
altConToHSE (DataAlt "(:)" [a1, a2]) =
    HSE.PInfixApp (HSE.PVar $ HSE.Ident a1) (HSE.Special HSE.Cons) (HSE.PVar $ HSE.Ident a2)

altConToHSE (DataAlt con args) =
    HSE.PApp (HSE.UnQual $ HSE.Ident con) (map (HSE.PVar . HSE.Ident) args)
altConToHSE (LiteralAlt lit) = HSE.PLit HSE.Signless $ litToHSE lit
altConToHSE (DefaultAlt Nothing) = HSE.PWildCard
altConToHSE (DefaultAlt (Just v)) = HSE.PVar (HSE.Ident v)

bindToHSE :: (Var, Term ann) -> HSE.Decl
bindToHSE (v, t) =
    case termToHSE t of
      HSE.Lambda _ pats body ->
        HSE.FunBind [HSE.Match dummyLoc (HSE.Ident v) pats Nothing (HSE.UnGuardedRhs body)
                      (HSE.BDecls [])]
      t' ->
        HSE.FunBind [HSE.Match dummyLoc (HSE.Ident v) [] Nothing (HSE.UnGuardedRhs t')
                      (HSE.BDecls [])]

litToHSE :: Literal -> HSE.Literal
litToHSE (Int i) = HSE.Int i
litToHSE (Char c) = HSE.Char c

app :: HSE.Exp -> [HSE.Exp] -> HSE.Exp
app = foldl' (flip HSE.App)

dummyLoc :: HSE.SrcLoc
dummyLoc = HSE.SrcLoc "" 0 0
