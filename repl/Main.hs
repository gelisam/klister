{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import Control.Exception
import Control.Lens hiding (argument)
import Control.Monad (forever)
import Control.Monad.Except
import Control.Monad.Reader

import Data.Foldable (for_)
import Data.IORef
import qualified Data.Map as Map
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Options.Applicative

import System.Exit (exitFailure, exitSuccess)
import System.IO

import Evaluator
import Expander
import ModuleName
import Parser
import Parser.Command
import PartialCore
import Phase
import Pretty
import SplitCore
import Syntax
import Value
import World

data Options = Options { optCommand :: CLICommand }
data RunOptions = RunOptions { runOptFile :: FilePath
                             , runOptWorld :: Bool
                             , runOptBindingInfo :: Bool
                             }
data ReplOptions = ReplOptions { replOptFile :: Maybe FilePath }

data CLICommand
  = Run RunOptions
  | Repl ReplOptions

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  (mainWithOptions =<< execParser opts) `catch`
    \(e :: SomeException) -> print e >> exitFailure
  where
    fileArg = argument str (metavar "FILE")
    runOptions = Run <$>
      (RunOptions <$>
       fileArg <*>
       switch ( long "world" <>
                short 'w' <>
                help "Print the whole world" ) <*>
       switch ( long "bindings" <>
                help "Dump information about bindings encountered" )
      )
    replOptions = Repl . ReplOptions <$> optional fileArg
    parser = Options <$>
      subparser
        ( (command "run" (info runOptions (progDesc "Run a file")))
        <> (command "repl" (info replOptions (progDesc "Use the REPL")))
        )
    opts = info parser mempty

mainWithOptions :: Options -> IO ()
mainWithOptions opts =
  case optCommand opts of
    Repl (ReplOptions Nothing) -> do
      ctx <- mkInitContext (KernelName kernelName)
      void $ execExpand initializeKernel ctx
      repl ctx initialWorld
    Repl (ReplOptions (Just file)) -> do
      (_mn, ctx, result) <- expandFile file
      repl ctx (view expanderWorld result)
    Run (RunOptions file showWorld dumpBindings) -> do
      (mn, _ctx, result) <- expandFile file
      when showWorld $
        prettyPrint $ view expanderWorld result
      when dumpBindings $
        prettyPrint $ view expanderGlobalBindingTable result
      case Map.lookup mn (view worldEvaluated (view expanderWorld result)) of
        Nothing -> fail "Internal error: module not evaluated"
        Just results -> do
          -- Show just the results of evaluation in the module the user
          -- asked to run
          for_ results $ \(EvalResult env coreExpr sch val) -> do
            putStr "Example: "
            prettyPrintEnv env coreExpr
            putStr " : "
            prettyPrint sch
            putStr " ↦ "
            prettyPrintLn val
  where expandFile file = do
          mn <- moduleNameFromPath file
          ctx <- mkInitContext mn
          void $ execExpand initializeKernel ctx
          st <- execExpand (visit mn >> getState) ctx
          case st of
            Left err -> prettyPrintLn err *> fail ""
            Right result ->
              pure (mn, ctx, result)


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
       tryCommand theWorld l $ \l' ->
         case readExpr "<repl>" l' of
           Left err -> T.putStrLn err
           Right ok ->
             do putStrLn "Parser output:"
                T.putStrLn (syntaxText ok)
                c <- execExpand (expandExpr ok) ctx
                case c of
                  Left err -> putStr "Expander error: " *>
                              prettyPrintLn err
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
