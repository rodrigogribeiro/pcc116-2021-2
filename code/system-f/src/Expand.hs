module Expand where

import qualified Data.Map as Map
import Syntax

-- expanding term definitions

type Ctx = Map.Map Name Term

expand :: Ctx -> Term -> Term
expand ctx e = undefined
