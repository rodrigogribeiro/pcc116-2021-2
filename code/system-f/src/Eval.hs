module Eval (norm) where

import Data.List (union)
import qualified Data.Map as Map

import Syntax
import TypeCheck

type Env = Map.Map Name Term

-- normalization

norm :: Env -> Term -> Term
norm env t
  = case whnf env t of
      Var v -> Var v
      Lam s _ e -> Lam s (TyVar "_") $ norm env e
      App e e' -> App (norm env e) (norm env e')
      Let n e e' -> Let n (norm env e) (norm env e')
      TApp e _ -> norm env e
      TLam _ e -> norm env e

-- computing until reach a weak head normal form

whnf :: Env -> Term -> Term
whnf _ (Let n e e')
  = beta (n,e) e'
whnf env (App m a)
  = let m' = whnf env m in
    case m' of
      Lam n _ e' -> whnf env $ beta (n,a) e'
      _  -> App m' a
whnf env (TApp m _) = whnf env m
whnf env (TLam _ t) = whnf env t
whnf env (Var v)
  = case Map.lookup v env of
      Just x ->
        case x of
          Var v' | v == v' -> x
          _ -> whnf env x
whnf _ t = t


beta :: (Name, Term) -> Term -> Term
beta (v,a) f
  = case f of
      Var s | s == v -> a
            | otherwise -> Var s
      Lam s _ e
        | s == v -> Lam s (TyVar "_") e
        | s `elem` fvs -> let s1 = newName s fvs
                          in Lam s1 (TyVar "_") $ beta (v,a) $ rename s s1 e
        | otherwise -> Lam s (TyVar "_") (beta (v,a) e)
      App e e' -> App (beta (v,a) e) (beta (v,a) e')
      TLam s t -> TLam s (beta (v,a) t)
      TApp t ty -> TApp (beta (v,a) t) ty
      Let n e e' -> Let n (beta (v,a) e) (beta (v,a) e')
  where
    fvs = fv a

fv :: Term -> [Name]
fv = fv' []
  where
    fv' acc (Var s)
      | s `elem` acc = []
      | otherwise = [s]
    fv' acc (Lam s _ t) = fv' (s : acc) t
    fv' acc (App e e') = fv' acc e `union` fv' acc e'
    fv' acc (Let _ e e') = fv' acc e `union` fv' acc e'
    fv' acc (TLam _ t) = fv' acc t
    fv' acc (TApp e _) = fv' acc e


rename :: Name -> Name -> Term -> Term
rename x x1 e
  = case e of
      Var s | s == x -> Var x1
            | otherwise -> e
      Lam s t b
        | s == x -> e
        | otherwise -> Lam s t (rename x x1 b)
      App l r -> App (rename x x1 l) (rename x x1 r)
      Let n e' e'' -> Let n (rename x x1 e') (rename x x1 e'')
      TLam s t -> TLam s (rename x x1 t)
      TApp t sig -> TApp (rename x x1 t) sig
