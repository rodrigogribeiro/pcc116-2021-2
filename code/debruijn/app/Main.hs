module Main where

import Syntax
import Parser
import Eval
import Expand
import Pretty

import Control.Monad
import Control.Monad.Trans
import qualified Data.Map as Map
import System.Console.Haskeline

type Ctx = Map.Map Name Term

process :: Ctx -> String -> IO Ctx
process ctx line = do
  let res = parseTerm line
  case res of
    Left _ -> do
      let d = parseDef line
      case d of
        Left err -> print err >> return ctx
        Right (Def n e) -> return (Map.insert n e ctx)
    Right ex -> do
      let
        e1 = expand ctx ex
        nm = norm e1
      putStrLn (prettyTerm nm)
      return ctx

main :: IO ()
main
  = runInputT defaultSettings (loop Map.empty)


loop :: Ctx -> InputT IO ()
loop ctx
  = do
     minput <- getInputLine "deBruijn> "
     case minput of
       Nothing -> outputStrLn "Goodbye."
       Just input ->
         case input of
           "quit" -> outputStrLn "Goodbye."
           "show-defs" -> (liftIO $ printCtx ctx) >> loop ctx
           _      ->
             do
                ctx' <- liftIO (process ctx input)
                loop ctx'


printCtx :: Ctx -> IO ()
printCtx
  = mapM_ step . Map.toList
   where
     step (n,e) = putStrLn $ prettyName n ++ " = " ++ prettyTerm e
