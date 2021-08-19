module Pretty (prettyTerm) where

import Prelude hiding ((<>))
import Text.PrettyPrint.HughesPJ
import Syntax


class Pretty a where
  ppr :: Int -> a -> Doc


parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

instance Pretty Name where
  ppr _ (Name n) = text n

instance Pretty Term where
  ppr d (Var n)
    = ppr d n
  ppr d e@(_ :@: _)
    = parensIf (d > 0) (ppr d f <+> sep (map (ppr (d + 1)) xs))
      where
        (f,xs) = viewApp e
  ppr d e@(Lam _ _)
    = parensIf (d > 0)(char '\\' <> hsep vars <+> char '.' <+> body)
      where
        vars = map (ppr 0) (viewVars e)
        body = ppr (d + 1) (viewBody e)


viewVars :: Term -> [Name]
viewVars (Lam n e) = n : viewVars e
viewVars _ = []

viewBody :: Term -> Term
viewBody (Lam _ e) = e
viewBody e = e

viewApp :: Term -> (Term, [Term])
viewApp (e1 :@: e2) = go e1 [e2]
  where
    go (a :@: b) xs = go a (b : xs)
    go f xs = (f, xs)
viewApp _ = error "not application"


prettyTerm :: Term -> String
prettyTerm = render . ppr 0
