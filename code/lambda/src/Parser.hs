module Parser (parseTerm) where

import Text.Parsec
import Text.Parsec.String (Parser)
import Text.Parsec.Language (haskellStyle)

import qualified Text.Parsec.Token as Tok

import Syntax


lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser style
  where
    ops = ["\\", "."]
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
      body <- term
      return (foldr Lam body vars)

basic :: Parser Term
basic = parens term <|>
        variable    <|>
        lambda

term :: Parser Term
term = foldl1 (:@:) <$> many1 basic

parseTerm :: String -> Either ParseError Term
parseTerm = parse (contents term) ""
