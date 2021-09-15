module Eval where

import qualified Data.Map as Map

import Syntax

-- a simple normalization by evalution implementation

-- value application

vapp :: Value -> Value -> Value
vapp (VAbs f) v = f v
vapp (VNeutral t) v = VNeutral (NApp t v)
vapp _ _ = error "impossible! vapp!"

-- evalution

type Env = Map.Map Name Value

eval :: Env -> Term -> Value
eval env (Var v)
  = maybe (VNeutral (NVar v))
          id
          (Map.lookup v env)
eval env (Lam n e)
  = VAbs (\ v -> eval (Map.insert n v env) e)
eval env (App e e')
  = vapp (eval env e) (eval env e')
eval env (Pi n t t')
  = VPi (eval env t)
        (\ v -> eval (Map.insert n v env) t')
eval _ (Set i)
  = VSet i
eval _ Nat
  = VNat
eval _ Zero
  = VZero
eval env (Succ e)
  = VSucc (eval env e)
eval env (NatElim n a z s)
  = f n'
  where
    n' = eval env n
    a' = eval env a
    z' = eval env z
    s' = eval env s
    f x = case x of
            VZero -> z'
            VSucc m ->
              vapp (vapp s' m) (f m)
            VNeutral m ->
              VNeutral (NNatElim m a' z' s')
            _ -> error "impossible! eval.NatElim!"
eval env (Id a t u)
  = VId (eval env a)
        (eval env t)
        (eval env u)
eval env (Refl e)
  = VRefl (eval env e)
eval env (J a p r t u e)
  = case eval env e of
      VRefl _ -> eval env r
      VNeutral e' ->
        VNeutral (NJ (eval env a)
                     (eval env p)
                     (eval env r)
                     (eval env t)
                     (eval env u)
                     e')
      _ -> error "impossible! eval.J!"


-- unquoting

fresh :: Int -> Name
fresh n = "x@" ++ show n

var :: Name -> Value
var n = VNeutral (NVar n)

unquote :: Int -> Value -> Term
unquote k (VAbs f)
  = let x = fresh k in
    Lam (fresh k) (unquote (k + 1) (f (var x)))
unquote k (VPi a b)
  = let x = fresh k in
    Pi x (unquote k a) (unquote (k + 1) (b (var x)))
unquote _ (VSet i)
  = Set i
unquote _ VNat
  = Nat
unquote _ VZero
  = Zero
unquote k (VSucc v)
  = Succ (unquote k v)
unquote k (VId a t u)
  = Id (unquote k a)
       (unquote k t)
       (unquote k u)
unquote k (VRefl t)
  = Refl (unquote k t)
unquote k (VNeutral t)
  = neutral k t
  where
    neutral _ (NVar x) = Var x
    neutral k' (NApp e e')
      = App (neutral k' e)
            (unquote k' e')
    neutral k' (NNatElim n a z s)
      = NatElim (neutral k' n)
                (unquote k' a)
                (unquote k' z)
                (unquote k' s)
    neutral k' (NJ a p r t' u e)
      = J (unquote k' a)
          (unquote k' p)
          (unquote k' r)
          (unquote k' t')
          (unquote k' u)
          (neutral k' e)


-- equality test

veq :: Int -> Value -> Value -> Bool
veq k t u = unquote k t == unquote k u
