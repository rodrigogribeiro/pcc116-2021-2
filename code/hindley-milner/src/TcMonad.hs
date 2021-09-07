module TcMonad where

import Syntax
import Pretty

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ hiding ((<>))

-- definition of the type environment

type Gamma = Map.Map Name Sigma

data Env
  = Env {
      uniqs :: Int
    }

-- definition of the type inference monad

type ErrMsg = Doc

type Tc a = ExceptT ErrMsg (StateT Int Identity) a

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Tc Tau
fresh
  = do
      i <- get
      put (i + 1)
      return (TyVar (TV $ letters !! i))

runTc :: Tc a -> Either ErrMsg a
runTc m = runIdentity (evalStateT (runExceptT m) 0)
