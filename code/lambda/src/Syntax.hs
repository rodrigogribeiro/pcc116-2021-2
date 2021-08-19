module Syntax where

-- syntax for the untyped lambda calculus

newtype Name = Name String
  deriving (Eq, Ord, Show)


data Term
  = Var Name
  | Term :@: Term
  | Lam Name Term
  deriving (Eq, Ord, Show)
