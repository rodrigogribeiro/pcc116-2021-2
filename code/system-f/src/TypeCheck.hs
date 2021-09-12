module TypeCheck (tc, newName) where

import Control.Monad.Except
import Control.Monad.Identity

import Data.Char
import qualified Data.Map as Map
import Data.List (union)

import Text.PrettyPrint.HughesPJ

import Syntax


-- definition of the typing context

type Gamma = Map.Map Name Sigma


-- type checker monad

type Tc a = ExceptT Doc Identity a

-- free variables

fv :: Sigma -> [Name]
fv = fv' []
  where
    fv' acc (TyVar v)
      | v `elem` acc = []
      | otherwise = [v]
    fv' acc (t :-> t')
      = fv' acc t `union` fv' acc t'
    fv' acc (ForAll v t)
      = fv' (v:acc) t

-- main function

tc :: Term -> Either Doc Sigma
tc e = runIdentity (runExceptT (typeCheck Map.empty e))

-- type checker definition

typeCheck :: Gamma -> Term -> Tc Sigma
typeCheck gamma (Var n)
  = case Map.lookup n gamma of
      Just sig -> return sig
      Nothing  -> throwError (text $ "Undefined variable:" ++ n)
typeCheck gamma (App e e')
  = do
      t1 <- typeCheck gamma e
      t2 <- typeCheck gamma e'
      case t1 of
        t :-> t' | t == t2 -> return t'
        _                  -> throwError (text "type application error")
typeCheck gamma (Lam n sig e)
  = do
      sig' <- typeCheck (Map.insert n sig gamma) e
      return (sig :-> sig')
typeCheck gamma (TLam n t)
  = ForAll n <$> typeCheck gamma t
typeCheck gamma (TApp t sig)
  = do
      sig' <- typeCheck gamma t
      case sig' of
        ForAll n tau -> return (reduce tau)
          where
            reduce (TyVar v)
              | n == v    = sig
              | otherwise = TyVar v
            reduce (ForAll n' sig1')
              | n == n' = ForAll n' sig1'
              | n' `elem` fv sig = let n1 = newName n' (fv sig)
                                   in ForAll n1 (reduce $ rename n' n1 sig1')
              | otherwise = ForAll n' (reduce sig')
            reduce (sig1 :-> sig1') = reduce sig1 :-> reduce sig1'
        _ -> throwError (text "type application error")
typeCheck gamma (Let n e e')
  = do
       sig <- typeCheck gamma e
       typeCheck (Map.insert n sig gamma) e'


rename :: Name -> Name -> Sigma -> Sigma
rename n n' (TyVar v)
  | v == n = TyVar n'
  | otherwise = TyVar v
rename n n' (ForAll s sig)
  | n == s = ForAll s sig
  | otherwise = ForAll s (rename n n' sig)
rename n n' (sig :-> sig')
  = rename n n' sig :-> rename n n' sig'

newName :: Name -> [Name] -> Name
newName n fvs
  = head $ filter (`notElem` fvs) $ (s ++) . show <$> [1..]
    where
      s = removeFromEnd isDigit n
      removeFromEnd p = reverse . dropWhile p . reverse
