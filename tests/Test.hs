{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad
import Data.Text (Text)
import qualified Data.Text as T

import Test.Tasty
import Test.Tasty.HUnit


import Alpha
import Core
import Core.Builder
import Expander
import Parser
import PartialCore
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
     [ ( "[lambda [x] x]"
       , lam $ \x -> pure x
       )
     , ( "42"
       , sig 42
       )
     , ( "[send-signal 0]"
       , sendSig =<< sig 0
       )
     ]
   ]

testExpander :: Text -> IO Core -> Assertion
testExpander input spec = do
  output <- spec
  case readExpr "<test suite>" input of
    Left err -> assertFailure (show err)
    Right expr -> do
      ctx <- mkInitContext
      c <- execExpand (initializeExpansionEnv *> expandExpr expr) ctx
      case c of
        Left err -> assertFailure (show err)
        Right expanded ->
          case runPartialCore $ unsplit expanded of
            Nothing -> assertFailure "Incomplete expansion"
            Just done -> assertAlphaEq (T.unpack input) output done

----------------------------
-- Stolen from HUnit

assertAlphaEq :: (AlphaEq a, Show a) => String -> a -> a -> Assertion
assertAlphaEq preface expected actual =
  unless (alphaEq actual expected) (assertFailure msg)
 where msg = (if null preface then "" else preface ++ "\n") ++
             "expected: " ++ show expected ++ "\n but got: " ++ show actual
