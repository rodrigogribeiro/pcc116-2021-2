module Main where

import Syntax
import Parser
import Eval
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
      let nm = norm ex
      putStrLn (prettyTerm nm)

main :: IO ()
main = runInputT defaultSettings loop
  where
  loop = do
    minput <- getInputLine "Untyped> "
    case minput of
      Nothing -> outputStrLn "Goodbye."
      Just input -> if input == "quit"
                    then outputStrLn "Goodbye."
                    else (liftIO $ process input) >> loop
