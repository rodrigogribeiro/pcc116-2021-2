module Syntax where

import Data.List

-- syntax for the untyped lambda calculus

newtype Name = Name String
  deriving (Eq, Ord, Show)


data Term
  = Var Name
  | Term :@: Term
  | Lam Name Term
  deriving (Eq, Ord, Show)


-- definitions

data Def
  = Def {
      name :: Name
    , term :: Term
    } deriving (Eq, Ord, Show)

fv :: Term -> [Name]
fv (Var n) = [n]
fv (Lam n e) = fv e \\ [n]
fv (e :@: e') = fv e `union` fv e'


bv :: Term -> [Name]
bv (Var _) = []
bv (Lam n e) = [n] `union` bv e
bv (e :@: e') = bv e `union` bv e'
