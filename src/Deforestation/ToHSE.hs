module Deforestation.ToHSE where

import Data.List (foldl')
import qualified Language.Haskell.Exts as HSE

import Deforestation.Syntax

toHSE :: TTerm -> HSE.Exp
toHSE (TVar v) = HSE.Var (HSE.UnQual (HSE.Ident v))
toHSE (TConstr constr ts) =
    foldl' (\e t -> HSE.App e (toHSE t)) (HSE.Con (HSE.UnQual (HSE.Ident constr))) ts
toHSE (TApp v0 vs) =
    foldl' (\e v -> HSE.App e (HSE.Var (HSE.UnQual (HSE.Ident v))))
           (HSE.Var (HSE.UnQual (HSE.Ident v0))) vs
toHSE (TCase v ps) = HSE.Case (toHSE (TVar v)) $ flip map ps $ \(Pat c vs, rhs) ->
                       HSE.Alt dummyLoc
                               (HSE.PApp (HSE.UnQual $ HSE.Ident c)
                                         (map (HSE.PVar . HSE.Ident) vs))
                               (HSE.UnGuardedRhs $ toHSE rhs)
                               (HSE.BDecls [])

ppFn :: (Var, ([Var], TTerm)) -> String
ppFn (fName, (args, body)) = HSE.prettyPrint $ HSE.FunBind
    [ HSE.Match dummyLoc (HSE.Ident fName) (map (HSE.PVar . HSE.Ident) args) Nothing
                (HSE.UnGuardedRhs $ toHSE body) (HSE.BDecls []) ]

dummyLoc :: HSE.SrcLoc
dummyLoc = HSE.SrcLoc "" 0 0
