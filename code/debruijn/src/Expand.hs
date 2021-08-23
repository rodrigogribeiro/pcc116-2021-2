-- |

module Expand (expand) where

import qualified Data.Map as Map

import Syntax

type Ctx = Map.Map Name Term

expand :: Ctx -> Term -> Term
expand ctx e@(Var v)
  = maybe e id (Map.lookup v ctx)
expand ctx (e :@: e')
  = (expand ctx e) :@: (expand ctx e')
expand ctx (Lam n e)
  = Lam n (expand (Map.delete n ctx) e)
