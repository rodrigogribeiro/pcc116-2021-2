module Parser where

import           Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token     as Token
import           Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Expr      as Expr

import Syntax

-- definition of the lexer

lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser style
  where ops = ["->","\\", "=", "::"]
        names = ["let", "in"]
        style = haskellStyle {Token.reservedOpNames = ops,
                              Token.reservedNames = names,
                              Token.commentLine = "#"}


-- definition of the parser

lamParser :: Parser Term -> Parser Term
lamParser p
  = do
       lexeme (char '\\')
       n <- nameParser
       lexeme (char '.')
       body <- p
       return (Lam n body)

nonApp :: Parser Term
nonApp = parens term     <|>
         lamParser term  <|>
         varParser       <|>
         litParser       <|>
         letParser term

letParser :: Parser Term -> Parser Term
letParser p
  = do
      Token.symbol lexer "let"
      (n,t) <- braces bindParser
      Token.symbol lexer "in"
      t' <- term
      return (Let n t t')

bindParser :: Parser (Name, Term)
bindParser
  = do
      n <- nameParser
      reservedOp "="
      t <- term
      return (n,t)

litParser :: Parser Term
litParser = Lit <$> integer

term :: Parser Term
term = chainl1 nonApp $ optional space >> return App

-- type parser

tyAtomParser :: Parser Tau
tyAtomParser
  = typeLitParser <|> parens typeParser

typeLitParser :: Parser Tau
typeLitParser
  = boolTyParser <|> intTyParser
  where
    boolTyParser = (TyCon BoolT) <$ reservedOp "bool"
    intTyParser = (TyCon IntT) <$ reservedOp "int"

typeParser :: Parser Tau
typeParser
  = Expr.buildExpressionParser tyops tyAtomParser
    where
      infixOp x f = Expr.Infix (f <$ reservedOp x)
      tyops = [[infixOp "->" Fun Expr.AssocRight]]

-- basic parsers

lexeme :: Parser a -> Parser a
lexeme = Token.lexeme lexer

nameParser :: Parser Name
nameParser = Token.identifier lexer

varParser :: Parser Term
varParser = Var <$> nameParser

parens :: Parser a -> Parser a
parens = Token.parens lexer

braces :: Parser a -> Parser a
braces = Token.braces lexer

integer :: Parser Int
integer = fromInteger <$> Token.integer lexer

reservedOp :: String -> Parser ()
reservedOp = Token.reservedOp lexer
