module Eval (norm) where

import qualified Data.Map as Map

import Syntax
import Pretty


-- value definition

data Value
  = VAbs (Value -> Value)
  | VNeutral Neutral

data Neutral
  = NVar Name
  | NApp Neutral Value


type Step = (Int, Term)

type Env = Map.Map Name Value

emptyEnv :: Env
emptyEnv = Map.empty

extend :: Name -> Value -> Env -> Env
extend n v = Map.insert n v

eval :: Env -> Term -> Value
eval env (Var n)
  = case Map.lookup n env of
      Just v -> v
      Nothing -> VNeutral (NVar n)
eval env (Lam n e)
  = VAbs (\ v -> eval (extend n v env) e)
eval env (e :@: e')
  = app (eval env e) (eval env e')

app :: Value -> Value -> Value
app (VAbs f) u = f u
app (VNeutral n) u = VNeutral (NApp n u)

fresh :: Int -> Name
fresh n = Name ("x" ++ (show n))

unquote :: Int -> Value -> Term
unquote n (VAbs f)
  = let
      x = fresh n
    in Lam x (unquote (n + 1) (f (VNeutral (NVar x))))
unquote n (VNeutral x)
  = neutral n x

neutral :: Int -> Neutral -> Term
neutral _ (NVar x) = Var x
neutral i (NApp n v) = (neutral i n) :@: (unquote i v)


norm :: Term -> Term
norm e = unquote 0 (eval emptyEnv e)
