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
    = text "Set_" <+> int i
  pretty (Pi n ty sig)
    = pI <+> parens pSig <+> dot <+> pretty sig
    where
      pSig = text n <+> dcolon <+> pretty ty
  pretty Nat = text "Nat"
  pretty Zero = text "zero"
  pretty (Succ n) = text "Succ" <> parens (pretty n)
  pretty (NatElim n ty z s)
    = text "NatElim"


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
