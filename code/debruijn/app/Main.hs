module Main where

import Syntax
import Parser
import DeBruijn
import Expand
import Pretty

import Control.Monad
import Control.Monad.Trans
import System.Console.Haskeline

process :: String -> IO ()
process line = do
  let res = parseTerm line
  case res of
    Left err -> print err
    Right ex -> do
      let
        nm = norm ex
      putStrLn (prettyTerm nm)

main :: IO ()
main
  = runInputT defaultSettings loop


loop :: InputT IO ()
loop
  = do
     minput <- getInputLine "deBruijn> "
     case minput of
       Nothing -> outputStrLn "Goodbye."
       Just input ->
         case input of
           "quit" -> outputStrLn "Goodbye."
           _      ->
             do
                liftIO (process input)
                loop
