module Syntax where

import qualified Data.Map as Map

-- term syntax definition

data Definition
  = Def Name Type Term
  deriving (Eq, Ord)

type Name = String

type Type = Term

data Term
  -- variables
  = Var Name
  -- lambda abstraction
  | Lam Name Term
  -- application
  | App Term Term
  -- universe type
  | Set Int
  -- function type
  | Pi Name Type Type
  -- natural numbers
  | Nat
  | Zero
  | Succ Term
  | NatElim Term Type Term Term
  -- equality type
  | Id Type Term Term
  -- equality introduction
  | Refl Term
  -- equality elimination
  | J Term Term Term Term Term Term
  deriving (Eq, Ord)

-- typing context

type Gamma = Map.Map Name Term

-- values

data Value
  -- lambda abstraction
  = VAbs (Value -> Value)
  -- pi type
  | VPi Value (Value -> Value)
  -- universe
  | VSet Int
  -- nat type
  | VNat
  -- zero
  | VZero
  -- succ
  | VSucc Value
  -- identity
  | VId Value Value Value
  -- refl
  | VRefl Value
  -- neutral
  | VNeutral Neutral

data Neutral
  -- names
  = NVar Name
  | NApp Neutral Value
  | NNatElim Neutral Value Value Value
  | NJ Value Value Value Value Value Neutral
