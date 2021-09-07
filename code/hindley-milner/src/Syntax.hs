module Syntax where


-- definition of the syntax of the
-- language of Hindley-Milner language.

-- 1. definition of types

type Name = String
type Uniq = Int

data TCon
  = IntT
  | BoolT
  deriving (Eq, Ord, Show)

data TVar
  = TV String
  deriving (Eq, Show, Ord)

intType :: Tau
intType = TyCon IntT

data Tau
  = Fun Tau Tau
  | TyCon TCon
  | TyVar TVar
  deriving (Eq, Ord, Show)

data Sigma
  = ForAll [TVar] Tau
    deriving (Eq, Ord, Show)

(-->) :: Tau -> Tau -> Tau
arg --> res = Fun arg res

-- 2. Term syntax

data Term
  = Var Name
  | Lit Int
  | App Term Term
  | Lam Name Term
  | Let Name Term Term
  deriving (Eq, Ord, Show)
