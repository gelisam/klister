{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Lens
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
import ShortShow
import SplitCore
import Syntax.SrcLoc
import Syntax

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Expander tests" [ miniTests ]

miniTests :: TestTree
miniTests =
  testGroup "Mini-tests" [ expectedSuccess, expectedFailure]
  where
    expectedSuccess =
      testGroup "Expected to succeed"
      [ testCase name (testExpander input output)
      | (name, input, output) <-
        [ ( "[lambda [x] x]"
          , "[lambda [x] x]"
          , lam $ \x -> x
          )
        , ( "[lambda [x] [lambda [x] x]]"
          , "[lambda [x] [lambda [x] x]]"
          , lam $ \_ -> lam $ \y -> y
          )
        , ( "42"
          , "42"
          , sig 42
          )
        , ( "[send-signal 0]"
          , "[send-signal 0]"
          , sendSig =<< sig 0
          )
        , ( "[lambda [f] [lambda [x] [f x]]]"
          , "[lambda [f] [lambda [x] [f x]]]"
          , lam $ \f -> lam $ \x -> f `app` x
          )
        , ( "Trivial user macro"
          , "[let-syntax \n\
            \  [m [lambda [_] \n\
            \       [pure [quote [lambda [x] x]]]]] \n\
            \  m]"
          , lam $ \x -> x
          )
        , ( "Let macro"
          , "[let-syntax \n\
            \  [let1 [lambda [stx] \n\
            \          (syntax-case stx \n\
            \            [[vec [_ binder body]] \n\
            \             (syntax-case binder \n\
            \               [[vec [x e]] \n\
            \                {- [[lambda [x] body] e] -} \n\
            \                [pure [vec-syntax \n\
            \                        [[vec-syntax \n\
            \                           [[ident lambda] \n\
            \                            [vec-syntax [x] stx] \n\
            \                            body] \n\
            \                           stx] \n\
            \                         e] \n\
            \                        stx]]])])]] \n\
            \  [let1 [x [lambda [x] x]] \n\
            \    x]]"
          , (lam $ \x -> x) `app` (lam $ \x -> x)
          )
        , ( "[if #t [lambda [x] x] #f]"
          , "[if #t [lambda [x] x] #f]"
          , iF (bool True) (lam $ \x -> x) (bool False)
          )
        ]
      ]
    expectedFailure =
      testGroup "Expected to fail"
      [ testCase (show input) (testExpansionFails input predicate)
      | (input, predicate) <-
        [ ( "x"
          , \case
              Unknown (Stx _ _ "x") -> True
              _ -> False
          )
        , ("[let-syntax \
           \  [m [lambda [_] \
           \       [pure [quote [lambda [x] x]]]]] \
           \  anyRandomWord]"
           , \case
               Unknown (Stx _ _ "anyRandomWord") -> True
               _ -> False
           )
        , ("[lambda [x] [let-syntax [m [lambda [_] x]] x]]"
          , \case
              Unknown (Stx _ _ "x") -> True
              _ -> False
          )
        , ("[let-syntax [m [lambda [x] [m x]]] m]"
          , \case
              Unknown (Stx _ loc "m") ->
                -- Make sure it's the use site in the macro body that
                -- throws the error
                view (srcLocStart . srcPosCol) loc == 29
              _ -> False
          )
        ]
      ]

testExpander :: Text -> IO Core -> Assertion
testExpander input spec = do
  output <- spec
  case readExpr "<test suite>" input of
    Left err -> assertFailure . T.unpack $ err
    Right expr -> do
      ctx <- mkInitContext
      c <- execExpand (initializeExpansionEnv *> expandExpr expr) ctx
      case c of
        Left err -> assertFailure . T.unpack . expansionErrText $ err
        Right expanded ->
          case runPartialCore $ unsplit expanded of
            Nothing -> assertFailure "Incomplete expansion"
            Just done -> assertAlphaEq (T.unpack input) output done

testExpansionFails :: Text -> (ExpansionErr -> Bool) -> Assertion
testExpansionFails input okp =
  case readExpr "<test suite>" input of
    Left err -> assertFailure . T.unpack $ err
    Right expr -> do
      ctx <- mkInitContext
      c <- execExpand (initializeExpansionEnv *> expandExpr expr) ctx
      case c of
        Left err
          | okp err -> return ()
          | otherwise ->
            assertFailure $ "An error was expected but not this one: " ++ show err
        Right expanded ->
          case runPartialCore $ unsplit expanded of
            Nothing -> assertFailure "Incomplete expansion"
            Just _ -> assertFailure "Error expected, but expansion succeeded"


----------------------------
-- Stolen from HUnit

assertAlphaEq :: (AlphaEq a, ShortShow a) => String -> a -> a -> Assertion
assertAlphaEq preface expected actual =
  unless (alphaEq actual expected) (assertFailure msg)
 where msg = (if null preface then "" else preface ++ "\n") ++
             "expected: " ++ shortShow expected ++ "\n but got: " ++ shortShow actual
