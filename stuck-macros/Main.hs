{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import Control.Lens hiding (argument)
import Control.Monad (forever)
import Control.Monad.Except
import Control.Monad.Reader

import Data.IORef
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Options.Applicative

import System.Exit (exitSuccess)
import System.IO

import Evaluator
import Expander
import Module
import Parser
import Parser.Command
import PartialCore
import Phase
import Pretty
import SplitCore
import Syntax
import Value
import World

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
      repl ctx initialWorld
    Just file ->
      execExpand (visit (ModuleName file) >> view expanderWorld <$> getState) ctx >>=
      \case
        Left err -> T.putStrLn (expansionErrText err)
        Right w -> repl ctx w

tryCommand :: IORef (World Value) -> T.Text -> (T.Text -> IO ()) -> IO ()
tryCommand w l nonCommand =
  case readCommand "<repl>" l of
    Right CommandQuit -> do
      putStrLn "Leaving."
      exitSuccess
    Right CommandWorld -> do
      theWorld <- readIORef w
      prettyPrint theWorld
      putStrLn ""
    Left err | T.isPrefixOf (T.pack ":") l -> T.putStrLn err
             | otherwise -> nonCommand l

repl :: ExpanderContext -> World Value -> IO ()
repl ctx startWorld = do
  theWorld <- newIORef startWorld
  forever $
    do putStr "> "
       l <- T.getLine
       tryCommand theWorld l $ \l' -> case readExpr "<repl>" l' of
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
                      currentWorld <- readIORef theWorld
                      runExceptT (runReaderT (runEval (eval expr)) (phaseEnv runtime currentWorld)) >>=
                        \case
                          Left evalErr -> print evalErr
                          Right val -> prettyPrint val >> putStrLn ""
