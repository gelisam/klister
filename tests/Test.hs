{-# LANGUAGE OverloadedStrings #-}
module Main where

import Data.Text (Text)

import Test.Tasty
import Test.Tasty.HUnit

import Alpha
import Core
import Expander
import Parser
import PartialCore
import Signals
import SplitCore

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Expander tests" [ miniTests ]

miniTests :: TestTree
miniTests =
  testGroup "Mini-tests"
   [ testCase (show input) (testExpander input output)
   | (input, output) <-
     [("[lambda [x] x]",
       Core (CoreSendSignal (Signal 0)))]
   ]

testExpander :: Text -> Core -> Assertion
testExpander input output =
  case readExpr "<test suite>" input of
    Left err -> assertFailure (show err)
    Right expr -> do
      ctx <- mkInitContext
      c <- execExpand (initializeExpansionEnv *> expandExpr expr) ctx
      case c of
        Left err -> assertFailure (show err)
        Right expanded ->
          case runPartialCore $ zonk expanded of
            Nothing -> assertFailure "Incomplete expansion"
            Just c -> assertFailure "unimplemented"
