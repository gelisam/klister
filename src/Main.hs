module Main where

import qualified Data.Text as T
import qualified Data.Text.IO as T

import System.IO

import Parser
import Syntax

main :: IO ()
main =
  hSetBuffering stdout NoBuffering *> repl

repl :: IO ()
repl =
  do putStr "> "
     l <- T.getLine
     case readExpr "<repl>" l of
       Left err -> T.putStrLn err
       Right ok -> T.putStrLn (syntaxText ok)
     repl
