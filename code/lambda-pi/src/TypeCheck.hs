module TypeCheck where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Identity

import qualified Data.Map as Map

import Syntax hiding (Gamma)
import Eval


-- monad definition

data Error
  = UnboundVar Name
  | TypeError
  deriving Show

type Tc a = ExceptT Error (StateT Int Identity) a

type Gamma = Map.Map Name Value

type Sigma = Value

runTc :: Tc a -> Either Error a
runTc m = runIdentity (evalStateT (runExceptT m) 0)

freshName :: Tc Name
freshName = get >>= return . fresh

inc :: Tc a -> Tc a
inc m
  = do
      n <- get
      put (n + 1)
      x <- m
      put n
      return x
-- type inference

undefinedVar :: Name -> Tc a
undefinedVar n = throwError (UnboundVar n)

infer :: Gamma -> Env -> Term -> Tc Sigma
infer gamma _ (Var v)
  = maybe (undefinedVar v)
          return
          (Map.lookup v gamma)
infer gamma env (App t u)
  = do
       sig <- infer gamma env t
       case sig of
         VPi a b ->
           do {
             check gamma env u a ;
             return (b (eval env u)) }
         _ -> throwError TypeError
infer gamma env (Pi n a b)
  = do
       i <- universe gamma env a
       let a' = eval env a
       j <- universe (Map.insert n a' gamma) env b
       return (VSet (i `max` j))
infer _ _ (Set i)
  = return (VSet i)
infer _ _ Nat
  = return (VSet 0)
infer _ _ Zero
  = return VNat
infer gamma env (Succ t)
  = do
      check gamma env t VNat
      return VNat
infer gamma env (NatElim n a z s)
  = do
      check gamma env n VNat
      let a' = eval env a
      case a' of
        VPi VNat a'' ->
          do
            let n' = eval env n
            check gamma env z (a'' VZero)
            check gamma env s (VPi VNat (\ m -> varr (a'' m)
                                        (a'' (VSucc m))))
            return (a'' n')
        _ -> throwError TypeError
infer gamma env (Id a t u)
  = do
      i <- universe gamma env a
      let a' = eval env a
      check gamma env t a'
      check gamma env u a'
      return (VSet i)
infer gamma env (Refl t)
  = do
      a <- infer gamma env t
      let t' = eval env t
      return (VId a t' t')
infer gamma env (J a p r t u e)
  = do
      i <- universe gamma env a
      let a' = eval env a
      check gamma env p (VPi a' (\ x -> VPi a' (\ y -> varr (VId a' x y)
                                                            (VSet i))))
      let p' = eval env p
      let q x y = vapp (vapp (vapp p' x) y)
      check gamma env r (VPi a' (\ x -> q x x (VRefl x)))
      check gamma env t a'
      check gamma env u a'
      let t' = eval env t
      let u' = eval env u
      check gamma env e (VId a' t' u')
      let e' = eval env e
      return (q t' u' e')
infer _ _ (Lam _ _) = throwError TypeError


varr :: Sigma -> Sigma -> Sigma
varr a b = VPi a (const b)


universe :: Gamma -> Env -> Type -> Tc Int
universe gamma env ty
  = do
      sig <- infer gamma env ty
      case sig of
        VSet i -> return i
        _      -> throwError TypeError

check :: Gamma -> Env -> Term -> Sigma -> Tc ()
check gamma env (Lam n t) (VPi a b)
  = do
       y <- var <$> freshName
       inc $ check (Map.insert n a gamma)
                   (Map.insert n y env)
                   t
                   (b y)
check gamma env (Refl t) (VId _ u v)
  = do
       let t' = eval env t
       k <- get
       unless (veq k t' u) (throwError TypeError)
       unless (veq k t' v) (throwError TypeError)
check gamma env t a
  = do
       a' <- infer gamma env t
       k <- get
       unless (veq k a' a) (throwError TypeError)
