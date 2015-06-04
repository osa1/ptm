{-# LANGUAGE LambdaCase #-}

module Deforestation.Parser where

import qualified Language.Haskell.Exts as HSE

import Deforestation.Syntax

-- (mostly copied from CoreLike.Parser)

parseTerm :: String -> Either String Term
parseTerm contents =
    case HSE.parseExp contents of
      HSE.ParseOk hse -> transformHSE hse
      HSE.ParseFailed loc str ->
        Left $ "fromParseResult: Parse failed at [" ++ HSE.srcFilename loc
                 ++ "] (" ++ show (HSE.srcLine loc) ++ ":"
                 ++ show (HSE.srcColumn loc) ++ "): " ++ str

parseTerm' :: String -> Term
parseTerm' = either error id . parseTerm

transformHSE :: HSE.Exp -> Either String Term
transformHSE (HSE.Var qname) = Var <$> transformQName qname
transformHSE (HSE.App e1 e2) = do
    e2' <- transformHSE e2
    transformHSE e1 >>= \case
      App v ts    -> return $ App v (ts ++ [e2'])
      Constr c ts -> return $ Constr c (ts ++ [e2'])
      Var v       -> return $ App v [e2']
      e           -> Left $ "Unsupported function in application syntax: " ++ show e
transformHSE (HSE.Case e alts) = Case <$> transformHSE e <*> mapM transformAlt alts
transformHSE (HSE.Paren e) = transformHSE e
transformHSE (HSE.Con qname) = flip Constr [] <$> transformQName qname
transformHSE e = Left $ "Unsupported HSE expression: " ++ show e

transformAlt :: HSE.Alt -> Either String (Pat, Term)
transformAlt (HSE.Alt _ pat rhs _) = (,) <$> transformPat pat <*> transformRhs rhs

transformPat :: HSE.Pat -> Either String Pat
transformPat (HSE.PApp qname pats) = Pat <$> transformQName qname <*> mapM collectArg pats
transformPat p = Left $ "transformPat: Unsupported pattern: " ++ show p

collectArg :: HSE.Pat -> Either String Var
collectArg (HSE.PVar v) = return $ nameVar v
collectArg p =
    Left $ "collectArgs: Unsupported pattern in function arguments: " ++ show p

transformRhs :: HSE.Rhs -> Either String Term
transformRhs (HSE.GuardedRhss rhss) = Left $ "Guarded RHSs are not supported: " ++ show rhss
transformRhs (HSE.UnGuardedRhs e) = transformHSE e

transformQName :: HSE.QName -> Either String Var
transformQName q@HSE.Qual{} = Left $ "Qualified names are not supported: " ++ show q
transformQName (HSE.UnQual n) = return $ nameVar n
transformQName (HSE.Special HSE.Cons) = return "(:)"
transformQName (HSE.Special HSE.UnitCon) = return "()"
transformQName (HSE.Special s) = Left $ "Unsupported special name: " ++ show s

nameVar :: HSE.Name -> Var
nameVar (HSE.Ident s)  = s
nameVar (HSE.Symbol s) = s
