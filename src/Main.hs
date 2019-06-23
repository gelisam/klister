module Main where

import Control.Monad (forever)

import qualified Data.Text as T
import qualified Data.Text.IO as T

import System.Exit (exitSuccess)
import System.IO

import Parser
import Parser.Command
import Syntax

main :: IO ()
main =
  hSetBuffering stdout NoBuffering *> repl

tryCommand :: T.Text -> (T.Text -> IO ()) -> IO ()
tryCommand l nonCommand =
  case readCommand "<repl>" l of
    Right Command_Quit -> do
      putStrLn "Leaving."
      exitSuccess
    Left err | T.isPrefixOf (T.pack ":") l -> T.putStrLn err
             | otherwise -> nonCommand l

repl :: IO ()
repl = forever $
  do putStr "> "
     l <- T.getLine
     tryCommand l $ \l -> case readExpr "<repl>" l of
       Left err -> T.putStrLn err
       Right ok ->
         do putStrLn "Parser output:"
            T.putStrLn (syntaxText ok)
            
