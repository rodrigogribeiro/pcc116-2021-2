module Pretty where

import Data.List (union)
import Prelude hiding ((<>))
import Text.PrettyPrint.HughesPJ

import Syntax


class Pretty a where
  pretty :: a -> Doc

instance Pretty Term where
  pretty (Var n) = text n
  pretty (Lam n t)
    = lam <+> text n <+> pretty t
  pretty (App t u)
    = parensWhen composite t <+> pretty u
  pretty (Set i)
    = text "Set:" <+> int i
  pretty (Pi n ty sig)
    = pI <+> parens pSig <+> dot <+> pretty sig
    where
      pSig = text n <+> dcolon <+> pretty ty
  pretty Nat = text "Nat"
  pretty Zero = text "zero"
  pretty (Succ n) = text "succ" <> parens (pretty n)
  pretty (NatElim n ty z s)
    = text "NatElim" <> ep
      where
        ep = pretty n <> comma <+> pretty ty
                       <> comma <+> pretty z
                       <> comma <+> pretty s
  pretty (Id ty t t')
    = text "Id" <> parens ep
      where
        ep = pretty ty <> comma <+> pretty t
                       <> comma <+> pretty t'
  pretty (Refl t)
    = text "refl" <> parens (pretty t)
  pretty (J a p r t u e)
    = text "J" <> parens ep
      where
        ep = pretty a <> comma <+> pretty p
                      <> comma <+> pretty r
                      <> comma <+> pretty t
                      <> comma <+> pretty u
                      <> comma <+> pretty e


prettyArrow :: Type -> Type -> Doc
prettyArrow t t'
  = pretty t <+> arrow <+> pretty t'

-- atomic

composite :: Term -> Bool
composite (Var _) = False
composite (Set _) = False
composite Nat = False
composite Zero = False
composite _ = True

-- basic constructions

parensWhen :: (Term -> Bool) -> Term -> Doc
parensWhen p t
  | p t = parens (pretty t)
  | otherwise = pretty t

refl :: Doc
refl = text "refl"

equal :: Doc
equal = text "=="

pI :: Doc
pI = text "Pi"

arrow :: Doc
arrow = text "->"

dcolon :: Doc
dcolon = text ":"

lam :: Doc
lam = text "\\"

dot :: Doc
dot = text "."
