module FlowChart.Lexer where

import Control.Monad
import Text.Parsec hiding (token)
import Text.Parsec.String

data Token
  = Symbol String   -- ^ Starts with lower case or tick(')
  | Variable String -- ^ Starts with capital letter
  | Asgn
  | Colon
  | SemiC
  | LParen
  | RParen
  | Comma
  deriving (Show, Eq)

type TokPos = (Token, SourcePos)

tokenize :: SourceName -> String -> Either ParseError [TokPos]
tokenize = runParser tokenize' ()

-- | Similar to Parsec's `testParser`.
testLexer :: String -> Either ParseError [TokPos]
testLexer = runParser tokenize' () ""

tokenize' :: Parser [TokPos]
tokenize' =
    -- We need to use `try` here, because we don't want to commit to `token`
    -- after parsing white space or a comment(using `ignore`, in definition of
    -- `token`).
    --
    -- Unfortunately this makes error messages worse. E.g. if we have a problem
    -- in top-level we get:
    --   expecting "--", space or end of input
    --
    -- Becuase `try token` always succeeds and it tries to parse `ignore >> eof`.
    many (try token) <* (ignore >> eof)

token :: Parser TokPos
token = ignore >> choice (map pos toks)
  where
    toks =
      [ Symbol        <$> ((:) <$> lower <*> many (alphaNum <|> char '_'))
      , Variable      <$> ((:) <$> upper <*> many (alphaNum <|> char '_'))
      , Symbol        <$> try (char '\'' >> string "()")
      , Symbol        <$> (char '\'' >> many1 alphaNum)
      , return Asgn   <*  try (string ":=")
      , return Colon  <*  char ':'
      , return SemiC  <*  char ';'
      , return LParen <*  char '('
      , return RParen <*  char ')'
      , return Comma  <*  char ','
      ]

ignore, comment :: Parser ()
ignore = skipMany (comment <|> void (many1 space))
comment = void $ string "--" >> manyTill anyChar newline

pos :: Parser a -> Parser (a, SourcePos)
pos p = flip (,) <$> getPosition <*> p
