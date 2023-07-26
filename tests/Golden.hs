-- make sure we don't accidentally change the result of any of the examples in
-- the 'examples' folder.
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Golden where

import Control.Lens hiding (argument)
import Control.Monad.Catch (bracket)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Writer (WriterT, execWriterT, tell)
import Data.Foldable (for_)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T
import System.FilePath (replaceExtension, takeBaseName)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (findByExtension, goldenVsStringDiff)
import qualified Data.HashMap.Strict as HM
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Encoding as TE
import System.IO (Handle, openFile, hClose, IOMode(WriteMode))
import System.IO.Silently (hCapture_)
import System.Directory

import Evaluator
import Expander
import Expander.Monad
import ModuleName
import Pretty
import World


mkGoldenTests :: IO TestTree
mkGoldenTests = do
  klisterFiles <- findByExtension [".kl"] "examples"
  return $ testGroup "Golden tests"
    [ let actual = execWriterT $ runExamples file
      in goldenVsStringDiff testName diffCmd goldenFile (TE.encodeUtf8 <$> actual)
    | file <- klisterFiles
    , let testName = takeBaseName file
    , let goldenFile = replaceExtension file ".golden"
    ]

diffCmd :: FilePath -> FilePath -> [String]
diffCmd goldenFile actualFile = ["diff", "-u", goldenFile, actualFile]

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
    expandFile magicHandle file >>= \case

      -- if we had an error or an expected failure then report it. Tasty-golden
      -- will track the failure
      Left err -> prettyTellLn err

      -- a normal test so all good
      Right (moduleName, result) ->
        case HM.lookup moduleName (view worldEvaluated (view expanderWorld result)) of
          Nothing      -> fail "Internal error: module not evaluated"
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

expandFile :: Handle -> FilePath -> WriterT Text IO (Either ExpansionErr (ModuleName, ExpanderState))
expandFile magicHandle file = do
  moduleName <- liftIO $ moduleNameFromPath file
  ctx <- liftIO $ getCurrentDirectory >>= mkInitContext moduleName
  void $ liftIO $ execExpand ctx (initializeKernel magicHandle)
  liftIO $ fmap (moduleName,) <$> execExpand ctx (visit moduleName >> getState)

prettyTell :: Pretty ann a
           => a -> WriterT Text IO ()
prettyTell = tell . Text.fromStrict . pretty

prettyTellLn :: Pretty ann a
             => a -> WriterT Text IO ()
prettyTellLn = tell . (<> "\n") . Text.fromStrict . pretty
