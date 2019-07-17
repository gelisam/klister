{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import Control.Monad (forever)
import Control.Monad.Except
import Control.Monad.Reader

import qualified Data.Text as T
import qualified Data.Text.IO as T

import Options.Applicative

import System.Exit (exitSuccess)
import System.IO

import qualified Env as Env
import Evaluator
import Expander
import Parser
import Parser.Command
import PartialCore
import Pretty
import SplitCore
import Syntax
import Value

data Options = Options { sourceModule :: Maybe FilePath }

main :: IO ()
main = execParser opts >>= mainWithOptions
  where
    opts = info parser mempty
    parser = Options <$> optional (argument str (metavar "FILE"))

mainWithOptions :: Options -> IO ()
mainWithOptions opts =
  case sourceModule opts of
    Nothing ->
      hSetBuffering stdout NoBuffering *> repl
    Just file ->
      readModule file >>=
      \case
        Left err -> T.putStrLn err
        Right contents -> do
          ctx <- mkInitContext
          done <- execExpand (initializeExpansionEnv *> expandModule contents) ctx
          case done of
            Left err -> do
              putStrLn "Expansion error"
              T.putStrLn (expansionErrText err)
            Right out -> do
              putStrLn "Expansion succeeded!"
              prettyPrint out
              putStrLn ""
              run <- runExceptT (runReaderT (runEval (evalMod out)) Env.empty)
              case run of
                Left err ->
                  putStrLn "Error when evaluating module examples" *>
                  print err
                Right examples ->
                  forM_ examples $ \(c, v) -> do
                    putStr "Example "
                    prettyPrint c
                    putStr " is "
                    print v

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
              Left err -> putStr "Expander error: " *>
                          T.putStrLn (expansionErrText err)
              Right (unsplit -> out) -> do
                putStrLn "Expander Output:"
                print out
                case runPartialCore out of
                  Nothing -> putStrLn "Expression incomplete, can't evaluate"
                  Just expr ->
                    putStrLn "Complete expression in core:" >>
                    prettyPrint expr >> putStrLn "" >>
                    runExceptT (runReaderT (runEval (eval expr)) Env.empty) >>=
                    \case
                      Left evalErr -> print evalErr
                      Right val -> T.putStrLn (valueText val)
