-- make sure we don't accidentally change the result of any of the examples in
-- the 'examples' folder.
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Golden where

import Control.Lens hiding (argument)
import Control.Monad.Catch (bracket)
import Control.Monad.Except
import Control.Monad.Trans.Writer (WriterT, execWriterT, tell)
import Data.Foldable (for_)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import System.Directory (doesFileExist)
import System.FilePath (replaceExtension, takeBaseName)
import Test.Tasty.HUnit (assertFailure, testCase)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (findByExtension)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.IO as Text
import System.IO (Handle, openFile, hClose, IOMode(WriteMode))
import System.IO.Silently (hCapture_)

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
    [ testCase testName $ do
        actual <- execWriterT $ runExamples klisterFile
        firstRun <- not <$> doesFileExist goldenFile
        when firstRun $ do
          putStrLn $ "first run: creating " ++ goldenFile
          Text.writeFile goldenFile actual
        expected <- Text.readFile goldenFile
        when (actual /= expected) $ do
          assertFailure . Text.unpack
                        $ "expected:\n" <> expected
                       <> "\ngot:\n" <> actual
    | klisterFile <- klisterFiles
    , let testName = takeBaseName klisterFile
    , let goldenFile = replaceExtension klisterFile ".golden"
    ]

runExamples :: FilePath -> WriterT Text IO ()
runExamples file = do
  -- We want to capture whatever the test writes to Klister's stdout without
  -- accidentally capturing what the test harness writes to Haskell's stdout.
  -- Here we create a Handle which is distinct from Haskell's stdout. Below, we
  -- use 'hCapture_' to replace it with a handle to which we can actually
  -- write, not /dev/null.
  bracket (liftIO $ openFile "/dev/null" WriteMode)
          (liftIO . hClose)
        $ \magicHandle -> do
    (moduleName, result) <- expandFile magicHandle file
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
              output <- liftIO $ hCapture_ [magicHandle] io
              tell (T.pack output)

expandFile :: Handle -> FilePath -> WriterT Text IO (ModuleName, ExpanderState)
expandFile magicHandle file = do
  moduleName <- liftIO $ moduleNameFromPath file
  ctx <- liftIO $ mkInitContext moduleName
  void $ liftIO $ execExpand ctx (initializeKernel magicHandle)
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
