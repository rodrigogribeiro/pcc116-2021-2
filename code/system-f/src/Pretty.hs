module Pretty where

import Prelude hiding ((<>))
import Text.PrettyPrint.HughesPJ
import Syntax

-- pretty printing

dot :: Doc
dot = char '.'

arrow :: Doc
arrow = text "->"

class Pretty a where
  ppr :: a -> Doc

instance Pretty Sigma where
  ppr (TyVar n) = text n
  ppr (sig :-> sig')
    | atomic sig = ppr sig <+>
                   arrow   <+>
                   ppr sig'
    | otherwise = parens (ppr sig) <+>
                  arrow            <+>
                  ppr sig'
  ppr (ForAll n sig) = text "forall" <+>
                       text n        <+>
                       dot           <>
                       ppr sig



instance Pretty Term where
  ppr (Var n) = text n
  ppr (Let n e e') = text "let" <+>
                     braces (nest 3 (pprBind n e)) <+>
                     text "in" <+> ppr e'
        where
          pprBind x t = text x <+> text "=" <+> ppr t
  ppr (Lam n sig e) = text "\\" <+>
                      text n    <+>
                      colon     <+>
                      ppr sig   <+>
                      dot       <+>
                      ppr e
  ppr (TLam n e) = text "/\\" <+>
                   text n     <>
                   dot        <+>
                   ppr e
  ppr (TApp e sig)
    | single e = ppr e <+> braces (ppr sig)
    | otherwise = parens (ppr e) <+> braces (ppr sig)
  ppr (App e e')
    | single e  = ppr e <+> ppr e'
    | otherwise = parens (ppr e) <+> ppr e'
