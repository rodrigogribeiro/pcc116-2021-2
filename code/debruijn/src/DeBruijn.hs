module DeBruijn where

import qualified Data.Map as Map
import Syntax

-- definition of the De Bruijn indices

data Bruijn
  = IVar Int
  | IApp Bruijn Bruijn
  | IAbs Bruijn
  deriving (Eq, Ord, Show)

-- conversion environment

type IEnv = [Name]

convert :: IEnv -> Term -> Bruijn
convert env (Var v) = IVar (position env)
  where
    position (y : ys)
      | y == v = 0
      | otherwise = 1 + position ys
    position _ = error "impossible!"
convert env (e :@: e') = IApp (convert env e) (convert env e')
convert env (Lam n e) = IAbs (convert (n : env) e)

fromTerm :: Term -> Bruijn
fromTerm = convert []

-- lifting of variables

lift :: Int -> Bruijn -> Bruijn
lift l (IVar i)
  | i >= l = IVar (i + 1)
  | otherwise = IVar i
lift l (IApp e e')
  = IApp (lift l e) (lift l e')
lift l (IAbs e)
  = IAbs (lift (l + 1) e)

unlift :: Int -> Int -> Int
unlift l i
  | l < i = i
  | otherwise = i - 1

sub :: Int -> Bruijn -> Bruijn -> Bruijn
sub i (IVar j) u
  | i == j = u
  | otherwise = IVar (unlift i j)
sub i (IApp e e') u
  = IApp (sub i e u) (sub i e' u)
sub i (IAbs e) u
  = IAbs (sub (i + 1) (lift 0 u) e)

-- call by value semantics

reduce :: Bruijn -> Bruijn
reduce v@(IVar _) = v
reduce v@(IAbs _) = v
reduce (IApp e e')
  = case reduce e of
      IAbs e1 -> sub 0 (reduce e') e1
      e1      -> IApp e1 (reduce e')


normalize :: Bruijn -> [Bruijn]
normalize e
  = let e' = reduce e
    in if e == e'
       then [e]
       else e : normalize e'
