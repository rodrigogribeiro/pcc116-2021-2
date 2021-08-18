-- |

module Search where

import Control.Monad

-- Implementação de cálculo de sequentes para proof search

-- formulas

data Prop
  = Falsum
  | Verum
  | Var String
  | And Prop Prop
  | Or  Prop Prop
  | Imp Prop Prop
  deriving (Eq, Ord, Show)

-- contexts and sequents

type Ctx = [Prop]

-- search algorithm

search :: Prop -> IO Bool
search = prove [] []

prove :: Ctx -> Ctx -> Prop -> IO Bool
prove _ _ Verum
  = pure True
prove env' env (And a b)
  = (&&) <$> prove env' env a <*>
             prove env' env b
prove env' env (Imp a b)
  = do
       prove env' (a : env) b
prove env' ((And b c) : env) a
  = prove env' (b : c : env) a
prove env' ((Or b c) : env) a
  = (&&) <$> prove env' (b : env) a <*>
             prove env' (c : env) a
prove env' (Verum : env) a
  = prove env' env a
prove env' (Falsum : env) a
  = return True
prove env' (Imp (And b c) d : env) a
  = prove env' (Imp b (Imp c d) : env) a
prove env' (Imp (Or b c) d : env) a
  = prove env' (Imp b d : Imp c d : env) a
prove env' (Imp Verum b : env) a
  = prove env' (b : env) a
prove env' (Imp Falsum b : env) a
  = prove env' env a
prove env' (b@(Var _) : env) a
  = prove (b : env') env a
prove env' (b@(Imp (Var _) _) : env) a
  = do
      prove (b : env') env a
prove env' (b@(Imp (Imp _ _) _) : env) a
  = prove (b : env') env a
prove env' [] v@(Var _)
  | v `elem` env' = return True
  | otherwise = foldM (cond v) False (contexts env')
prove env' [] (Or a b)
  = (||) <$> prove env' [] a <*> prove env' [] b
prove env' [] a
  = foldM (cond a) False (contexts env')

cond a ac (Imp x@(Var _) b,env'')
  | x `elem` env'' =  prove env'' [b] a
  | otherwise = return ac
cond a ac (Imp (Imp b c) d, env'')
  = (&&) <$> prove env'' [Imp c d] (Imp b c) <*>
             prove env'' [d] a
cond _ ac _ = return ac

contexts :: Eq a => [a] -> [(a,[a])]
contexts xs = [(x, filter (/= x) xs) | x <- xs]


-- test case

imp1 :: Prop
imp1 = Imp (Var "A") (Var "B")

imp2 :: Prop
imp2 = Imp (Var "B") (Var "C")

imp3 :: Prop
imp3 = Imp (Var "A") (Var "C")

test :: Prop
test = Imp imp1 (Imp imp2 imp3)
