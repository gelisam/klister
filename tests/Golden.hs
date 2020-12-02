-- make sure we don't accidentally change the result of any of the examples in
-- the 'examples' folder.
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Golden where

import Control.Lens hiding (argument)
import Control.Monad.Except
import Control.Monad.Trans.Writer (WriterT, execWriterT, tell)
import Data.Foldable (for_)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import System.FilePath (replaceExtension, takeBaseName)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (findByExtension, goldenVsStringDiff)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Encoding as Text
import System.IO.Silently (capture_)

import Evaluator
import Expander
import Expander.Monad
import ModuleName
import Pretty
import World


mkGoldenTests :: IO TestTree
mkGoldenTests = do
  allKlisterFiles <- findByExtension [".kl"] "examples"
  let klisterFiles :: [FilePath]
      klisterFiles = filter (not . ("/non-examples/" `List.isInfixOf`))
                   . filter (not . ("/failing-examples/" `List.isInfixOf`))
                   $ allKlisterFiles
  return $ testGroup "Golden tests"
    [ goldenVsStringDiff testName diffCmd goldenFile $ do
        outputLines <- execWriterT $ runExamples klisterFile
        pure . Text.encodeUtf8 $ outputLines
    | klisterFile <- klisterFiles
    , let testName = takeBaseName klisterFile
    , let goldenFile = replaceExtension klisterFile ".golden"
    ]

diffCmd :: FilePath -> FilePath -> [String]
diffCmd goldenFile actualFile = ["diff", "-u", goldenFile, actualFile]

runExamples :: FilePath -> WriterT Text IO ()
runExamples file = do
  (moduleName, result) <- expandFile file
  case Map.lookup moduleName (view worldEvaluated (view expanderWorld result)) of
    Nothing -> fail "Internal error: module not evaluated"
    Just results -> do
      -- Show just the results of evaluation in the module the user
      -- asked to run
      for_ results $
        \case
          (ExampleResult _ _ _ tp val) -> do
            prettyTell val
            tell " : "
            prettyTellLn tp
          (IOResult io) -> do
            output <- liftIO $ capture_ io
            tell (T.pack output)
  where

expandFile :: FilePath -> WriterT Text IO (ModuleName, ExpanderState)
expandFile file = do
  moduleName <- liftIO $ moduleNameFromPath file
  ctx <- liftIO $ mkInitContext moduleName
  void $ liftIO $ execExpand ctx initializeKernel
  st <- liftIO $ execExpand ctx (visit moduleName >> getState)
  case st of
    Left err -> liftIO $ prettyPrintLn err *> fail ""
    Right result ->
      pure (moduleName, result)

prettyTell :: Pretty ann a
           => a -> WriterT Text IO ()
prettyTell = tell . Text.fromStrict . pretty

prettyTellLn :: Pretty ann a
             => a -> WriterT Text IO ()
prettyTellLn = tell . (<> "\n") . Text.fromStrict . pretty
