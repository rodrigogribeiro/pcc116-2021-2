module Pretty where

import Prelude hiding ((<>))

import Syntax

import Text.PrettyPrint.HughesPJ


-- definition of a class for pretty
-- printing values

class Pretty a where
  ppr :: a -> Doc

-- basic documents

dcolon :: Doc
dcolon = text "::"

dot :: Doc
dot = char '.'

pprName :: String -> Doc
pprName = text


-- printing terms


instance Pretty Term where
  ppr (Var v) = pprName v
  ppr (Lit i) = int i
  ppr e@(App _ _) = pprApp e
  ppr (Lam n e)
    = sep [char '\\' <> pprName n <> dot, ppr e]
  ppr (Let n rhs e)
    = sep [ text "let {"
          , nest 2 (pprName n <+> equals <+> ppr rhs <+> char '}')
          , text "in"
          , ppr e]

atomic :: Term -> Bool
atomic (Var _) = True
atomic (Lit _) = True
atomic _       = False

pprParensTerm :: Term -> Doc
pprParensTerm e
  | atomic e = ppr e
  | otherwise = parens (ppr e)


pprApp :: Term -> Doc
pprApp e = go e []
  where
    go (App e1 e2) acc = go e1 (e2 : acc)
    go e' acc = pprParensTerm e' <+> sep (map pprParensTerm acc)


-- printing types

type Precedence = Int

topPrec :: Precedence
topPrec = 0

arrPrec :: Precedence
arrPrec = 1

tcPrec :: Precedence
tcPrec = 2

atomicPrec :: Precedence
atomicPrec = 3

precType :: Tau -> Precedence
precType (Fun _ _)    = arrPrec
precType _            = atomicPrec

pprParensType :: Tau -> Doc
pprParensType = pprType tcPrec

pprType :: Precedence -> Tau -> Doc
pprType p ty
  | p >= precType ty = parens (pprTy ty)
  | otherwise = pprTy ty

pprTy :: Tau -> Doc
pprTy (Fun arg res)
  = sep [ pprType arrPrec arg <+> text "->"
        , pprType (arrPrec - 1) res]
pprTy (TyCon tc)
  = ppr tc
pprTy (TyVar v)
  = ppr v

instance Pretty Tau where
  ppr = pprTy

instance Pretty Sigma where
  ppr (ForAll vs ty)
    | null vs = pprType topPrec ty
    |  otherwise
       = sep [ text "forall" <+>
               hsep (map ppr vs) <> dot
             , ppr ty]


instance Pretty TVar where
  ppr (TV n) = text n

instance Pretty TCon where
  ppr IntT = text "int"
  ppr BoolT = text "bool"
