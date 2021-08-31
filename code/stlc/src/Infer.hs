module Infer where

import STLC
import qualified Data.Map as Map

-- Explaining the reason of errors

type Expected = Ty
type Found = Ty

data Error
  = UndefinedVar Name
  | CheckError Expected Found
  | ExpectedFunction Found
  deriving (Eq, Ord, Show)

-- inference algorithm

infer :: Gamma -> Term -> Either Error Ty
infer gamma (Var v)
  = case Map.lookup v gamma of
      Just ty -> Right ty
      Nothing -> Left (UndefinedVar v)
infer gamma (Lam n ty e)
  = case infer gamma' e of
      Left err  -> Left err
      Right ty' -> Right (ty :-> ty')
    where
      gamma' = Map.insert n ty gamma
infer gamma (e :@: e')
  = case infer gamma e of
      Right (ty :-> ty') ->
        case infer gamma e' of
          Right ty1 ->
            if ty == ty1
            then Right ty'
            else Left (CheckError ty ty1)
      Right ty -> Left (ExpectedFunction ty)
      Left err -> Left err

-- checking algorithm

check :: Gamma -> Term -> Ty -> Either Error ()
check gamma e ty
  = case infer gamma e of
      Right ty' ->
        if ty == ty' then Right ()
        else Left (CheckError ty ty')
      Left err -> Left err
