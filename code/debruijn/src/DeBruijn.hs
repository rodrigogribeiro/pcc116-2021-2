module DeBruijn where

import Control.Monad.State

import qualified Data.Map as Map
import Prelude hiding ((<>))

import Text.PrettyPrint.HughesPJ

import Syntax

-- nameless terms

type Idx = Int

data Exp
  = EVar Name Idx
  | ELam Name Exp
  | EApp Exp Exp
  deriving (Eq, Ord, Show)

type NCtx = Map.Map Name Int

mkNameContext :: Term -> NCtx
mkNameContext e
  = Map.fromList values
  where
    values = zip bs [0..] ++ zip fs [n ..]
    bs = bv e
    n = length bs
    fs = fv e

removeNames :: NCtx -> Term -> Exp
removeNames env (Var n)
  = case Map.lookup n env of
      Just idx -> EVar n idx
      Nothing  -> error "removeNames"
removeNames env (Lam n e)
  = ELam n (removeNames env e)
removeNames env (e :@: e')
  = EApp (removeNames env e)
         (removeNames env e')

restoreNames :: NCtx -> Exp -> Term
restoreNames _ (EVar n _)
  = Var n
restoreNames env (ELam n e)
  = Lam n (restoreNames env e)
restoreNames env (EApp e1 e2)
  = restoreNames env e1 :@: restoreNames env e2

-- shifting names

shift :: Int -> Name -> Int -> Exp -> Exp
shift offset nspace minidx e
  = case e of
      EVar nm idx -> EVar nm idx'
        where
          idx' = if nm == nspace && minidx <= idx
                 then idx + offset
                 else idx
      ELam nm ex -> ELam nm ex'
        where
          minIdx'
            | nm == nspace = minidx + 1
            | otherwise = minidx
          ex' = shift offset nspace minIdx' ex
      EApp ex ex' -> EApp (shift offset nspace minidx ex)
                          (shift offset nspace minidx ex')

-- substitution

subst :: Exp -> Name -> Int -> Exp -> Exp
subst expr nm idx rep
  = case expr of
      EVar nm' idx'
        | nm == nm' && idx == idx' -> rep
        | otherwise -> EVar nm' idx'
      ELam nm' bd -> ELam nm' bd'
        where
          index'
            | nm == nm' = idx + 1
            | otherwise = idx
          sbd = shift 1 nm' 0 rep
          bd' = subst bd nm index' sbd
      EApp ex ex' -> EApp (subst ex nm idx rep)
                          (subst ex' nm idx rep)

-- reduction

reduction :: Exp -> Exp
reduction v@(EVar _ _) = v
reduction (ELam n bd) = ELam n bd
reduction (EApp ex ex')
  = case ex of
      (ELam n bd) -> bd'
        where
          sarg = shift 1 n 0 ex'
          sbd = subst bd n 0 sarg
          usbd = shift (-1) n 0 sbd
          bd' = reduction usbd
      _ -> EApp (reduction ex)
                (reduction ex')

-- normalization

normExp :: Exp -> Exp
normExp e
  = let e' = reduction e
    in if e == e' then e
       else normExp e'

norm :: Term -> Term
norm e
  = restoreNames ctx r
  where
    ctx = mkNameContext e
    e' = removeNames ctx e
    r  = normExp e'
