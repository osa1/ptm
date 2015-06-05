module Deforestation.ToHSE (ppTerm, ppTTerm, ppFn) where

import Data.List (foldl')
import qualified Language.Haskell.Exts as HSE

import Deforestation.Syntax

ttToHSE :: TTerm -> HSE.Exp
ttToHSE (TVar v) = HSE.Var (HSE.UnQual (HSE.Ident v))
ttToHSE (TConstr c ts) =
    foldl' (\e t -> HSE.App e (ttToHSE t)) (HSE.Con (HSE.UnQual (HSE.Ident c))) ts
ttToHSE (TApp v0 vs) =
    foldl' (\e v -> HSE.App e (HSE.Var (HSE.UnQual (HSE.Ident v))))
           (HSE.Var (HSE.UnQual (HSE.Ident v0))) vs
ttToHSE (TCase v ps) =
    HSE.Case (ttToHSE (TVar v)) $ flip map ps $ \(Pat c vs, rhs) ->
      HSE.Alt dummyLoc
              (HSE.PApp (HSE.UnQual $ HSE.Ident c)
                        (map (HSE.PVar . HSE.Ident) vs))
              (HSE.UnGuardedRhs $ ttToHSE rhs)
              (HSE.BDecls [])

ppFn :: (Var, ([Var], TTerm)) -> String
ppFn (fName, (args, body)) = HSE.prettyPrint $ HSE.FunBind
    [ HSE.Match dummyLoc (HSE.Ident fName) (map (HSE.PVar . HSE.Ident) args) Nothing
                (HSE.UnGuardedRhs $ ttToHSE body) (HSE.BDecls []) ]

ppTTerm :: TTerm -> String
ppTTerm = HSE.prettyPrint . ttToHSE

termToHSE :: Term -> HSE.Exp
termToHSE (Var v) = HSE.Var (HSE.UnQual (HSE.Ident v))
termToHSE (Constr c ts) =
    foldl' (\e t -> HSE.App e (termToHSE t)) (HSE.Con (HSE.UnQual (HSE.Ident c))) ts
termToHSE (App f ts) =
    foldl' (\e t -> HSE.App e (termToHSE t)) (HSE.Var (HSE.UnQual (HSE.Ident f))) ts
termToHSE (Case t ps) =
    HSE.Case (termToHSE t) $ flip map ps $ \(Pat c vs, rhs) ->
      HSE.Alt dummyLoc (HSE.PApp (HSE.UnQual $ HSE.Ident c)
                                 (map (HSE.PVar . HSE.Ident) vs))
                       (HSE.UnGuardedRhs $ termToHSE rhs)
                       (HSE.BDecls [])

ppTerm :: Term -> String
ppTerm = HSE.prettyPrint . termToHSE

dummyLoc :: HSE.SrcLoc
dummyLoc = HSE.SrcLoc "" 0 0
