module Main where

import Control.Monad.Trans
import qualified Data.Map as Map
import System.Console.Haskeline
import Text.PrettyPrint.HughesPJ

import Syntax
import TypeCheck
import Parser
import Eval
import Pretty

type Ctx = Map.Map Name Term



main :: IO ()
main = runInputT defaultSettings (loop Map.empty)


process :: Ctx -> String -> IO Ctx
process ctx line = do
  let res = parseCmd line
  case res of
    Left err -> print err >> return ctx
    Right ex ->
      case ex of
        None -> return ctx
        Def n t -> return (Map.insert n t ctx)
        Eval t ->
          do
            let n = norm ctx t
            putStrLn (render $ ppr n)
            return ctx


loop :: Ctx -> InputT IO ()
loop ctx
  = do
      inp <- getInputLine "system-f>"
      case inp of
        Nothing -> outputStrLn "Goodbye!"
        Just input ->
          case input of
            "quit" -> outputStrLn "Goodbye!"
            "show-defs" -> (liftIO $ printCtx ctx) >> loop ctx
            _ -> do
                    ctx' <- liftIO (process ctx input)
                    loop ctx'



printCtx :: Ctx -> IO ()
printCtx
  = mapM_ step . Map.toList
   where
     step (n,e) = putStrLn $ n ++ " = " ++ (render $ ppr e)
