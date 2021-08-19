module Parser (parseTerm, parseDef) where

import Text.Parsec
import Text.Parsec.String (Parser)
import Text.Parsec.Language (haskellStyle)

import qualified Text.Parsec.Token as Tok

import Syntax


lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser style
  where
    ops = ["\\", ".", "="]
    names = []
    style = haskellStyle {
              Tok.reservedOpNames = ops,
              Tok.reservedNames = names,
              Tok.commentLine = "#"
            }

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

identifier :: Parser Name
identifier = Name <$> Tok.identifier lexer

parens :: Parser a -> Parser a
parens = Tok.parens lexer

contents :: Parser a -> Parser a
contents p = Tok.whiteSpace lexer *> p <* eof

variable :: Parser Term
variable = Var <$> identifier

lambda :: Parser Term
lambda
  = do
      reservedOp "\\"
      vars <- many1 identifier
      reservedOp "."
      body <- expr
      return (foldr Lam body vars)

basic :: Parser Term
basic = parens expr <|>
        variable    <|>
        lambda

expr :: Parser Term
expr = foldl1 (:@:) <$> many1 basic

def :: Parser Def
def = f <$> identifier <*> eq <*> expr
  where
    eq = reservedOp "="
    f n _ e = Def n e

parseTerm :: String -> Either ParseError Term
parseTerm = parse (contents expr) ""

parseDef :: String -> Either ParseError Def
parseDef = parse (contents def) ""
