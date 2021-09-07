{-# LANGUAGE FlexibleInstances #-}

module Infer where

import           Control.Monad
import           Control.Monad.Except
import qualified Data.Map       as Map
import qualified Data.Set       as Set
import           Text.PrettyPrint.HughesPJ

import TcMonad
import Syntax
import Pretty


-- definition of type substitution

type Subst = Map.Map TVar Tau

(@@) :: Subst -> Subst -> Subst
s1 @@ s2 = Map.map (apply s1) s2 `Map.union` s1

idSubst :: Subst
idSubst = Map.empty

-- applying a substitution to a type

class Apply a where
  apply :: Subst -> a -> a
  fv    :: a -> Set.Set TVar

instance Apply Tau where
  apply s t@(TyVar v)
    = Map.findWithDefault t v s
  apply s (Fun arg res)
    = Fun (apply s arg)
          (apply s res)
  apply _ t@(TyCon _)
    = t

  fv (TyVar v) = Set.singleton v
  fv (Fun arg res) = fv arg `Set.union` fv res
  fv (TyCon _) = Set.empty

instance Apply Sigma where
  apply s (ForAll vs tau)
    = ForAll vs (apply s' tau)
      where
        s' = foldr Map.delete s vs
  fv (ForAll vs tau)
    = fv tau `Set.difference` Set.fromList vs

instance Apply Gamma where
  apply s = fmap (apply s)
  fv = foldr (Set.union . fv) Set.empty

-- type instantiation

instantiate :: Sigma -> Tc Tau
instantiate (ForAll vs rho)
  = do
      let
        step acc v
          = do
              v' <- fresh
              return (Map.insert v v' acc)
      s <- foldM step idSubst vs
      return (apply s rho)

-- type generalization

names :: [Name]
names = [1..] >>= flip replicateM ['a' .. 'z']

generalization :: Gamma -> Tau -> Sigma
generalization gamma tau
  = ForAll vs tau
    where
      vs = Set.toList $ fv tau `Set.difference` fv gamma


-- type unification

occurs :: TVar -> Tau -> Bool
occurs v tau = v `Set.member` (fv tau)

(+->) :: TVar -> Tau -> Tc Subst
v +-> tau
  | occurs v tau = throwError (text "Occurs check error!")
  | tau == (TyVar v) = return idSubst
  | otherwise = return (Map.singleton v tau)

unify :: Tau -> Tau -> Tc Subst
unify (Fun arg1 res1) (Fun arg2 res2)
  = do
      s1 <- unify arg1 arg2
      s2 <- unify (apply s1 res1)
                  (apply s1 res2)
      return (s2 @@ s1)
unify (TyVar v) tau = v +-> tau
unify tau (TyVar v) = v +-> tau
unify (TyCon tc1) (TyCon tc2)
  | tc1 == tc2 = return idSubst
  | otherwise  = throwError (text "Unification error!")
unify _ _ = throwError (text "Unification error!")

-- inference algorithm

lookupVar :: Gamma -> Name -> Tc (Subst, Tau)
lookupVar gamma v
  = case Map.lookup v gamma of
        Just sig ->
          do
            tau <- instantiate sig
            return (idSubst, tau)
        Nothing -> throwError (text "Not in scope:" <+> quotes (pprName v))


infer :: Gamma -> Term -> Tc (Subst, Tau)
infer gamma (Var v)
  = lookupVar gamma v
infer gamma (Lit _)
  = return (idSubst, intType)
infer gamma (Lam n e)
  = do
      t <- fresh
      let
          gamma' = Map.insert n (ForAll [] t) gamma
      (s', t') <- infer gamma' e
      return (s', apply s' (t --> t'))
infer gamma (App fun arg)
  = do
      v <- fresh
      (s1, t1) <- infer gamma fun
      (s2, t2) <- infer (apply s1 gamma) arg
      s3 <- unify (apply s2 t1) (t2 --> v)
      return (s3 @@ s2 @@ s1, apply s3 v)
infer gamma (Let n e e')
  = do
       (s1, t1) <- infer gamma e
       let gamma' = apply s1 gamma
           sig = generalization gamma' t1
       (s2, t2) <- infer (Map.insert n sig gamma') e'
       return (s2 @@ s1, t2)

-- top level type inference function

typeInfer :: Term -> Either ErrMsg Tau
typeInfer e
  = either Left
           (Right . snd)
           (runTc (infer Map.empty e))
