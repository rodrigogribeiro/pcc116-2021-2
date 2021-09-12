module Syntax where

-- definition of types

type Name = String

data Sigma
  = TyVar Name
  | ForAll Name Sigma
  | Sigma :-> Sigma
  deriving (Ord, Show)

swap :: (a,b) -> (b,a)
swap (x,y) = (y,x)

instance Eq Sigma where
  t1 == t2 = f [] t1 t2 where
    f alpha (TyVar s) (TyVar t)
      | Just t' <- lookup s alpha = t' == t
      | Just _ <- lookup t (swap <$> alpha) = False
      | otherwise = s == t
    f alpha (ForAll s x) (ForAll t y)
      | s == t    = f alpha x y
      | otherwise = f ((s, t):alpha) x y
    f alpha (a :-> b) (c :-> d) = f alpha a c && f alpha b d
    f _ _ _ = False

atomic :: Sigma -> Bool
atomic (TyVar _) = True
atomic _         = False

-- definition of terms

data Term
  = Var Name
  | App Term Term
  | Lam Name Sigma Term
  | Let Name Term Term
  | TLam Name Term
  | TApp Term Sigma
  deriving (Eq, Ord, Show)

single :: Term -> Bool
single (Var _) = True
single _       = False

