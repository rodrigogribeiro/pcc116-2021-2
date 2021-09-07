module Main where

import Syntax
import Pretty
import Parser
import Infer

import qualified Data.Map as Map

import System.Environment (getArgs)
import Text.PrettyPrint.HughesPJ
import Text.ParserCombinators.Parsec


main :: IO ()
main
  = do
      args <- getArgs
      case args of
        [] -> putStrLn "Please inform a term to infer the types"
        (s : _) -> exec s

exec :: String -> IO ()
exec s
  = case parse term "" s of
      Left err -> print err
      Right e  ->
          case typeInfer e of
            Left err' -> print err'
            Right ty  -> showResult ty

-- here, we do like GHCi, we generalize the types.

showResult :: Tau -> IO ()
showResult tau
  = do
      let sig = generalization Map.empty tau
      putStrLn (render (ppr sig))
