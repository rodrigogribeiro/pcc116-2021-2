module STLC where

import Data.Map

-- definition of types

type Name = String

data Ty
  = TVar Name
  | Ty :-> Ty
  deriving (Eq, Ord, Show)

-- contexts are finite maps between names and types

type Gamma = Map Name Ty

-- definition of terms, Church style

data Term
  = Var Name
  | Lam Name Ty Term
  | Term :@: Term
  deriving (Eq, Ord, Show)

