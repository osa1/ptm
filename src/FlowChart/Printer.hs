module FlowChart.Printer (pprintPgm) where

import Data.Char (toLower)
import Data.List (intersperse)
import Data.Maybe (catMaybes)
import Text.PrettyPrint.Leijen

import FlowChart.Syntax

pprintPgm :: Program -> String
pprintPgm pgm = displayS (renderPretty 0.8 100 (ppPgm pgm)) ""

ppPgm :: Program -> Doc
ppPgm (Program vs bs) = vcat $
      (text "read" <> tupled (map text vs) <> semi)
    : intersperse empty (map ppBlock bs)

ppBlock :: BasicBlock -> Doc
ppBlock (BasicBlock l asgns jmp) =
    -- one of the things I hate about `vcat`(or `<$$>`) is that `empty`
    -- is not unit
    vcat $ catMaybes $
       (Just $ text l <> colon)
     : (if null asgns then Nothing else Just $ indent 2 $ vcat $ map ppAsgn asgns)
     : fmap (indent 2 . ppJmp) jmp
     : []

ppAsgn :: Assignment -> Doc
ppAsgn (Assignment v e) = text v <+> text ":=" <+> ppExpr e

ppJmp :: Jump -> Doc
ppJmp (Goto lbl)    = text "goto" <+> text lbl
ppJmp (If c l1 l2)  = hsep
    [ text "if", ppExpr c, text "then", text l1, text "else", text l2 ]
ppJmp Halt          = text "halt()"
ppJmp (Panic e)     = text "panic" <> parens (ppExpr e)

ppExpr :: Expr -> Doc
ppExpr (Constant v) = ppVal v
ppExpr (Var v)      = text v
ppExpr (Op op es)   = text (map toLower $ show op) <> tupled (map ppExpr es)

ppVal :: Val -> Doc
ppVal (VSymbol s) = char '\'' <> text s
ppVal (VList vs)  = list $ map ppVal vs
