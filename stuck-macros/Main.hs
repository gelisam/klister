{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import Control.Monad (forever)
import Control.Monad.Except
import Control.Monad.Reader

import Data.IORef
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Options.Applicative

import System.Exit (exitSuccess)
import System.IO

import Env (Env)
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
main = do
  hSetBuffering stdout NoBuffering
  mainWithOptions =<< execParser opts
  where
    opts = info parser mempty
    parser = Options <$> optional (argument str (metavar "FILE"))

mainWithOptions :: Options -> IO ()
mainWithOptions opts = do
  ctx <- mkInitContext
  _ <- execExpand initializeExpansionEnv ctx
  case sourceModule opts of
    Nothing ->
      repl ctx Env.empty
    Just file ->
      readModule file >>=
      \case
        Left err -> T.putStrLn err
        Right contents -> do
          done <- execExpand (expandModule contents) ctx
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
                Right (modEnv, examples) -> do
                  forM_ examples $ \(env, c, v) -> do
                    putStr "Example "
                    prettyPrintEnv env c
                    putStr " is "
                    prettyPrintEnv env v
                    putStrLn ""
                  repl ctx modEnv

tryCommand :: T.Text -> (T.Text -> IO ()) -> IO ()
tryCommand l nonCommand =
  case readCommand "<repl>" l of
    Right Command_Quit -> do
      putStrLn "Leaving."
      exitSuccess
    Left err | T.isPrefixOf (T.pack ":") l -> T.putStrLn err
             | otherwise -> nonCommand l

repl :: ExpanderContext -> Env Value -> IO ()
repl ctx startEnv = do
  theEnv <- newIORef startEnv
  forever $
    do putStr "> "
       l <- T.getLine
       tryCommand l $ \l' -> case readExpr "<repl>" l' of
         Left err -> T.putStrLn err
         Right ok ->
           do putStrLn "Parser output:"
              T.putStrLn (syntaxText ok)
              c <- execExpand (expandExpr ok) ctx
              case c of
                Left err -> putStr "Expander error: " *>
                            T.putStrLn (expansionErrText err)
                Right (unsplit -> out) -> do
                  putStrLn "Expander Output:"
                  print out
                  case runPartialCore out of
                    Nothing -> putStrLn "Expression incomplete, can't evaluate"
                    Just expr -> do
                      putStrLn "Complete expression in core:"
                      prettyPrint expr
                      putStrLn ""
                      currentEnv <- readIORef theEnv
                      runExceptT (runReaderT (runEval (eval expr)) currentEnv) >>=
                        \case
                          Left evalErr -> print evalErr
                          Right val -> prettyPrint val >> putStrLn ""
