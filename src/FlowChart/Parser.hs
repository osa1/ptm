module FlowChart.Parser where

import Control.Monad.Identity
import Text.Parsec as P

import FlowChart.Lexer
import FlowChart.Syntax

tok :: Token -> ParsecT [TokPos] u Identity Token
tok t = P.token show snd match
  where
    match :: TokPos -> Maybe Token
    match (t', _) = if t == t' then Just t' else Nothing

symbol :: ParsecT [TokPos] u Identity String
symbol = P.token show snd match
  where
    match (Symbol s, _) = Just s
    match _             = Nothing

variable :: ParsecT [TokPos] u Identity String
variable = P.token show snd match
  where
    match (Variable v, _) = Just v
    match _               = Nothing

type Parser a = ParsecT [TokPos] () Identity a

program :: Parser Program
program = do
    -- programs always start with `read(vars)`
    void $ tok (Symbol "read") >> tok LParen
    vs <- variable `sepBy` tok Comma
    void $ tok RParen >> tok SemiC
    blocks <- many basicBlock
    eof
    return $ Program vs blocks

basicBlock :: Parser BasicBlock
basicBlock = do
    lbl   <- symbol <* tok Colon
    asgns <- many (assignment <* tok SemiC)
    ret   <- optionMaybe (jump <* tok SemiC)
    return $ BasicBlock lbl asgns ret

assignment :: Parser Assignment
assignment = do
    v <- variable
    void $ tok Asgn
    e <- expr
    return $ Assignment v e

jump :: Parser Jump
jump = choice
    [ goto, ifThenElse, halt, panic ]
  where
    goto = Goto <$> (tok (Symbol "goto") >> symbol)

    ifThenElse = do
      void $ tok (Symbol "if")
      cond <- expr
      void $ tok (Symbol "then")
      l1 <- symbol
      void $ tok (Symbol "else")
      l2 <- symbol
      return $ If cond l1 l2

    halt = tok (Symbol "halt") >> tok LParen >> tok RParen >> return Halt

    panic = Panic <$> (tok (Symbol "panic") >> tok LParen >> expr <* tok RParen)

expr :: Parser Expr
expr = choice
    -- We need to be careful with the order here, `op` is trying to parse a
    -- lowercase string so it can be confused with symbols parser.
    [ try $ uncurry Op <$> op
    , Constant <$> val
    , Var <$> variable
    ]

op :: Parser (Op, [Expr])
op = (,) <$> opName <*> between (tok LParen) (tok RParen) (expr `sepBy` tok Comma)

opName :: Parser Op
opName = choice . map mkP $ ops
  where
    ops = [ ("eq", Eq), ("hd", Hd), ("tl", Tl), ("cons", Cons), ("read", Read),
            ("rest", Rest), ("first_instruction", FirstInstruction),
            ("firstsym", FirstSym), ("new_tail", NewTail) ]
    mkP (n, ret) = tok (Symbol n) >> return ret

val :: Parser Val
val = VSymbol <$> symbol

-- | Similar to Parsec's `testParser`.
testFCP :: Parser a -> String -> Either ParseError a
testFCP p s = do
    toks <- testLexer s
    runParser p () "" toks
