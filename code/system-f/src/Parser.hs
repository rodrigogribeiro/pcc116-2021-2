module Parser where

import           Control.Monad
import           Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token     as Token
import           Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Expr      as Expr

import Syntax

-- definition of a command for the interpreter

data Cmd
  = None
  | Def Name Term
  | Eval Term
  deriving Show

-- parsing commands

cmdParser :: Parser Cmd
cmdParser
  = (<* eof) . (ws >>) $ option None $
    (try $ Def <$> nm <*> (str "=" >> term)) <|>
    (Eval <$> term)
    where
      str = try . (>> ws) . string
      braces = between (str "[") (str "]")
      term = letx <|> lam <|> app
      app = termArg >>= moreArg
      termArg = (Var <$> nm) <|> between (str "(") (str ")") term
      moreArg t = option t $ ((App t <$> termArg) <|>
                              (TApp t <$> between (str "[") (str "]") typ))
                              >>= moreArg
      lam = (termLam <|> tyLam) <*> term
      tyLam = do
                str "/\\"
                n <- nm
                str "."
                return (TLam n)
      termLam = do
                  str "\\"
                  n <- nm
                  str ":"
                  t <- typ
                  return (Lam n t)
      typ = forallt <|> fun
      forallt = flip (foldr ForAll) <$> between (str "forall") (str ".") (many1 nm) <*> fun
      fun = (TyVar <$> nm) <|> between (str "(") (str ")") typ `chainr1`
                               (str "->" >> pure (:->))
      ws = spaces >> optional (try $ string "--" >> many anyChar)
      nm = try $ do {
                  s <- many1 alphaNum
                ; when (s `elem` words "let in forall") $
                      fail "unexpected keyword"
                ; ws
                ; return s
                }

      letx = do
               str "let"
               (n,t) <- braces $ do {
                          n <- nm
                        ; str "="
                        ; t <- term
                        ; return (n, t)
                        }
               str "in"
               t' <- term
               return (Let n t t')
