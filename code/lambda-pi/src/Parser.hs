module Parser where

import Control.Monad

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Tok

import Syntax


-- lexer definition

lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser style
  where
    ops = ["\\", ".", "=", ":"]
    names = ["Id", "Set", "zero"
            , "succ", "Nat", "NatElim"
            , "refl", "J", "Pi"]
    style = haskellStyle {
              Tok.reservedOpNames = ops,
              Tok.reservedNames = names,
              Tok.commentLine = "#"
            }


-- parser definition

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

identifier :: Parser Name
identifier = Tok.identifier lexer

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
basic
  = choice [ parens expr
           , variable
           , lambda
           , succp
           , zerop
           , natp
           , setp
           , reflp
           , idp
           ]

succp :: Parser Term
succp = Succ <$> expr

zerop :: Parser Term
zerop = Zero <$ reserved "zero"

natp :: Parser Term
natp = Nat <$ reserved "Nat"

expr :: Parser Term
expr = foldl1 App <$> many1 basic

setp :: Parser Term
setp = Set <$> (reserved "Set:" *> natural)

reflp :: Parser Term
reflp
  = do
      reserved "refl"
      Refl <$> parens expr

idp :: Parser Term
idp
   = f <$> (reserved "Id" *> parens triple)
     where
        f (x,y,z) = Id x y z
        triple = do
               e1 <- expr
               comma
               e2 <- expr
               comma
               e3 <- expr
               return (e1, e2, e3)

jp :: Parser Term
jp = do
        reserved "NatElim"
        f <$> parens
          (do
            e1 <- expr
            comma
            e2 <- expr
            comma
            e3 <- expr
            comma
            e4 <- expr
            comma
            e5 <- expr
            comma
            e6 <- expr
            return (e1,e2,e3,e4,e5,e6))
      where
        f (a,b,c,d,e,g) = J a b c d e g



natural :: Parser Int
natural
  = fromInteger <$> Tok.natural lexer

params :: Parser [Term]
params
  = parens $ sepBy expr comma

comma :: Parser ()
comma = void $ Tok.symbol lexer ","
