{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import Control.Monad (forever)
import Control.Monad.Except
import Control.Monad.Reader

import qualified Data.Text as T
import qualified Data.Text.IO as T

import System.Exit (exitSuccess)
import System.IO

import qualified Env as Env
import Evaluator
import Expander
import Parser
import Parser.Command
import PartialCore
import SplitCore
import Syntax
import Value

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
     tryCommand l $ \l' -> case readExpr "<repl>" l' of
       Left err -> T.putStrLn err
       Right ok ->
         do putStrLn "Parser output:"
            T.putStrLn (syntaxText ok)
            ctx <- mkInitContext
            c <- execExpand (initializeExpansionEnv *> expandExpr ok) ctx
            case c of
              Left err -> putStr "Expander error: " *> print err
              Right (unsplit -> out) -> do
                putStrLn "Expander Output:"
                print out
                case runPartialCore out of
                  Nothing -> putStrLn "Expression incomplete, can't evaluate"
                  Just expr ->
                    runExceptT (runReaderT (runEval (eval expr)) Env.empty) >>=
                    \case
                      Left evalErr -> print evalErr
                      Right val -> T.putStrLn (valueText val)
