{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import Control.Lens hiding (List)
import Control.Monad
import Data.Text (Text)
import qualified Data.Text as T

import Test.Tasty
import Test.Tasty.HUnit


import Alpha
import Core
import Core.Builder
import Expander
import Expander.Monad
import Module
import ModuleName
import Parser
import PartialCore
import Phase (prior, runtime, Phased(..))
import Pretty
import Scope
import qualified ScopeSet
import ShortShow
import Signals
import SplitCore
import Syntax.SrcLoc
import Syntax
import World

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Expander tests" [ operationTests, miniTests, moduleTests ]

operationTests :: TestTree
operationTests =
  testGroup "Core operations"
  [ testCase "Shifting core expressions" $
    let sc = Scope 42
        scs = ScopeSet.insertAtPhase runtime sc ScopeSet.empty
        stx = Syntax (Stx scs fakeLoc (Id "hey"))
        expr = Core (CoreIf (Core (CoreBool True))
                            (Core (CoreSyntax stx))
                            (Core (CoreBool False)))
    in case shift 1 expr of
         Core (CoreIf (Core (CoreBool True))
                      (Core (CoreSyntax stx'))
                      (Core (CoreBool False))) ->
           case stx' of
             Syntax (Stx scs' _ (Id "hey")) ->
               if scs' == ScopeSet.insertAtPhase (prior runtime) sc ScopeSet.empty
                 then pure ()
                 else assertFailure $ "Shifting gave wrong scopes" ++ show scs'
             Syntax _ -> assertFailure "Wrong shape in shifted syntax"
         _ -> assertFailure "Shifting didn't preserve structure!"
  ]

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
        , ( "send a signal nobody is waiting for"
          , "[let-syntax \n\
            \  [signaling-id [lambda [_] \n\
            \                  [>>= [send-signal 0] [lambda [_] \n\
            \                  [pure [quote [lambda [x] x]]]]]]] \n\
            \    [let-syntax \n\
            \      [blocked-id [lambda [_] \n\
            \                    [>>= [wait-signal 0] [lambda [_] \n\
            \                    [pure [quote [lambda [x] x]]]]]]] \n\
            \        [signaling-id]]]"
          , lam $ \x -> x
          )
        , ( "send and receive the same signal"
          , "[let-syntax \n\
            \  [signaling-id [lambda [_] \n\
            \                  [>>= [send-signal 0] [lambda [_] \n\
            \                  [pure [quote [lambda [x] x]]]]]]] \n\
            \    [let-syntax \n\
            \      [blocked-id [lambda [_] \n\
            \                    [>>= [wait-signal 0] [lambda [_] \n\
            \                    [pure [quote [lambda [x] x]]]]]]] \n\
            \        [[signaling-id] [blocked-id]]]]"
          , (lam $ \x -> x) `app` (lam $ \x -> x)
          )
        ]
      ]
    expectedFailure =
      testGroup "Expected to fail"
      [ testCase name (testExpansionFails input predicate)
      | (name, input, predicate) <-
        [ ( "unbound variable and nothing else"
          , "x"
          , \case
              Unknown (Stx _ _ "x") -> True
              _ -> False
          )
        , ( "unbound variable inside let-syntax"
          , "[let-syntax \
            \  [m [lambda [_] \
            \       [pure [quote [lambda [x] x]]]]] \
            \  anyRandomWord]"
            , \case
                Unknown (Stx _ _ "anyRandomWord") -> True
                _ -> False
            )
        , ( "refer to a local variable from a future phase"
          , "[lambda [x] [let-syntax [m [lambda [_] x]] x]]"
          , \case
              Unknown (Stx _ _ "x") -> True
              _ -> False
          )
        , ( "a macro calls itself"
          , "[let-syntax [m [lambda [x] [m x]]] m]"
          , \case
              Unknown (Stx _ loc "m") ->
                -- Make sure it's the use site in the macro body that
                -- throws the error
                view (srcLocStart . srcPosCol) loc == 29
              _ -> False
          )
        , ( "wait for a signal which is never coming"
          , "[let-syntax \n\
            \  [signaling-id [lambda [_] \n\
            \                  [>>= [send-signal 0] [lambda [_] \n\
            \                  [pure [quote [lambda [x] x]]]]]]] \n\
            \    [let-syntax \n\
            \      [blocked-id [lambda [_] \n\
            \                    [>>= [wait-signal 0] [lambda [_] \n\
            \                    [pure [quote [lambda [x] x]]]]]]] \n\
            \        [blocked-id]]]"
          , \case
              NoProgress [AwaitingSignal _ (Signal 0) _] -> True
              _ -> False
          )
        , ( "send and receive different signals"
          , "[let-syntax \n\
            \  [signaling-id [lambda [_] \n\
            \                  [>>= [send-signal 0] [lambda [_] \n\
            \                  [pure [quote [lambda [x] x]]]]]]] \n\
            \    [let-syntax \n\
            \      [blocked-id [lambda [_] \n\
            \                    [>>= [wait-signal 1] [lambda [_] \n\
            \                    [pure [quote [lambda [x] x]]]]]]] \n\
            \        [[signaling-id] [blocked-id]]]]"
          , \case
              NoProgress [AwaitingSignal _ (Signal 1) _] -> True
              _ -> False
          )
        ]
      ]

moduleTests :: TestTree
moduleTests = testGroup "Module tests" [ shouldWork, shouldn'tWork ]
  where
    shouldWork =
      testGroup "Expected to succeed"
      [ testCase fn (testFile fn p)
      | (fn, p) <-
        [ ( "examples/small.kl"
          , \m -> isEmpty (view moduleBody m)
          )
        , ( "examples/id-compare.kl"
          , \m ->
              view moduleBody m & map (view completeDecl) &
              filter (\case {(Example _) -> True; _ -> False}) &
              \case
                [Example e1, Example e2] -> do
                  assertAlphaEq "first example" e1 (Core (CoreBool True))
                  assertAlphaEq "second example" e2 (Core (CoreBool False))
                _ -> assertFailure "Expected two examples"
          )
        , ( "examples/lang.kl"
          , \m ->
              view moduleBody m & map (view completeDecl) &
              \case
                [Define _fn fv fbody, Example e] -> do
                  fspec <- lam \_x -> lam \ y -> lam \_z -> y
                  assertAlphaEq "definition of f" fbody fspec
                  case e of
                    Core (CoreApp (Core (CoreApp (Core (CoreApp (Core (CoreVar fv')) _)) _)) _) ->
                      assertAlphaEq "function position in example" fv' fv
                    _ -> assertFailure "example has wrong shape"
                _ -> assertFailure "Expected two examples"
          )
        , ( "examples/import.kl"
          , \m ->
              view moduleBody m & map (view completeDecl) &
              filter (\case {(Example _) -> True; _ -> False}) &
              \case
                [Example e1, Example e2] -> do
                  case e1 of
                    (Core (CoreApp (Core (CoreApp (Core (CoreVar _)) _)) _)) ->
                      pure ()
                    _ -> assertFailure "example 1 has wrong shape"
                  case e2 of
                    Core (CoreApp (Core (CoreApp (Core (CoreApp fun _)) _)) _) -> do
                      fspec <- lam \_x -> lam \ y -> lam \_z -> y
                      assertAlphaEq "function in second example" fun fspec
                    _ -> assertFailure "example 2 has wrong shape"
                _ -> assertFailure "Expected two examples"
          )
        , ( "examples/phase1.kl"
          , \m ->
              view moduleBody m & map (view completeDecl) &
              \case
                [Import _,
                 Meta (view completeDecl -> Define _ _ _),
                 DefineMacros [(_, _, _)],
                 Example ex] ->
                  assertAlphaEq "Example is signal" ex (Core (CoreSignal (Signal 1)))
                _ -> assertFailure "Expected an import, a meta-def, a macro def, and an example"
          )
        , ( "examples/imports-shifted-macro.kl"
          , \m ->
              view moduleBody m & map (view completeDecl) &
              \case
                [Import _, Import _, DefineMacros [(_, _, _)], Example ex] ->
                  assertAlphaEq "Example is #f" ex (Core (CoreBool False))
                _ -> assertFailure "Expected import, import, macro, example"
          )
        , ( "examples/macro-body-shift.kl"
          , \m ->
              view moduleBody m & map (view completeDecl) &
              \case
                [Import _, Define _ _ e, DefineMacros [(_, _, _)]] -> do
                  spec <- lam \_x -> lam \y -> lam \_z -> y
                  assertAlphaEq "Definition is λx y z . y" e spec
                _ -> assertFailure "Expected an import, a definition, and a macro"
          )
        , ( "examples/quasiquote.kl"
          , \m ->
              view moduleBody m & map (view completeDecl) &
              \case
                (Import _ : DefineMacros [_, _] : Define _ _ thingDef : examples) -> do
                  case thingDef of
                    Core (CoreSyntax (Syntax (Stx _ _ (Id "nothing")))) ->
                      case examples of
                        [e1, e2, e3, e4, e5, e6, e7, e8, Export _, Export _ ] -> do
                          testQuasiquoteExamples [e1, e2, e3, e4, e5, e6, e7, e8]
                        other -> assertFailure ("Expected 8 examples and 2 exports: " ++ show other)
                    other -> assertFailure ("Unexpected thing def " ++ show other)
                _ -> assertFailure "Expected an import, two macros, a definition, and examples"
          )
        , ( "examples/quasiquote-syntax-test.kl"
          , \m ->
              view moduleBody m & map (view completeDecl) &
              \case
                (Import _ : Define _ _ thingDef : examples) -> do
                  case thingDef of
                    Core (CoreSyntax (Syntax (Stx _ _ (Id "nothing")))) ->
                      case examples of
                        [e1, e2, e3, e4, e5, e6, e7, e8] -> do
                          testQuasiquoteExamples [e1, e2, e3, e4, e5, e6, e7, e8]
                        other -> assertFailure ("Expected 8 examples and 2 exports: " ++ show other)
                    other -> assertFailure ("Unexpected thing def " ++ show other)
                _ -> assertFailure "Expected an import, two macros, a definition, and examples"
          )
        ]
      ]
    shouldn'tWork =
      testGroup "Expected to fail"
      [ testCase fn (testFileError fn p)
      | (fn, p) <-
        [ ( "examples/non-examples/import-phase.kl"
          , \case
              Unknown (Stx _ _ "define") -> True
              _ -> False
          )
        , ( "examples/non-examples/missing-import.kl"
          , \case
              NotExported (Stx _ _ "magic") p -> p == runtime
              _ -> False
          )
        ]
      ]


    isEmpty [] = return ()
    isEmpty _ = assertFailure "Expected empty, got non-empty"

testQuasiquoteExamples :: Show decl => [Decl decl Core] -> IO ()
testQuasiquoteExamples examples =
  case examples of
    [ Example e1, Example e2, Example e3, Example e4,
      Example e5, Example e6, Example e7, Example e8 ] -> do
      case e1 of
        Core (CoreVar _) -> pure ()
        other -> assertFailure ("Expected a var ref, got " ++ show other)
      case e2 of
        Core (CoreSyntax (Syntax (Stx _ _ (Id "thing")))) -> pure ()
        other -> assertFailure ("Expected thing, got " ++ show other)
      assertAlphaEq "Third and first example are the same" e3 e1
      case e4 of
        Core (CoreVec (ScopedVec [Core (CoreSyntax (Syntax (Stx _ _ (Id "thing"))))] _)) -> pure ()
        other -> assertFailure ("Expected [thing], got " ++ shortShow other)
      case e5 of
        Core (CoreVec (ScopedVec [expr] _)) -> assertAlphaEq "the expression is e1" expr e1
        other -> assertFailure ("Expected [nothing], got " ++ shortShow other)
      case e6 of
        Core (CoreVec (ScopedVec [(Core (CoreSyntax (Syntax (Stx _ _ (Id "vec-syntax")))))
                                 , Core (CoreVec (ScopedVec [expr, Core (CoreSyntax (Syntax (Stx _ _ (Id "thing"))))] _))
                                 , Core (CoreSyntax (Syntax (Stx _ _ (Id "thing"))))]
                        _)) -> assertAlphaEq "the expression is e1" expr e1
        other -> assertFailure ("Expected [vec-syntax [nothing thing] thing], got " ++ shortShow other)
      case e7 of
        Core (CoreVec (ScopedVec [(Core (CoreSyntax (Syntax (Stx _ _ (Id "vec-syntax")))))
                                 , Core (CoreVec (ScopedVec [ expr
                                                            , Core (CoreSyntax (Syntax (Stx _ _ (Id "thing"))))
                                                            , Core (CoreEmpty (ScopedEmpty _))]
                                                   _))
                                 , Core (CoreSyntax (Syntax (Stx _ _ (Id "thing"))))]
                        _)) -> assertAlphaEq "the expression is e1" expr e1
        other -> assertFailure ("Expected [vec-syntax [nothing thing ()] thing], got " ++ shortShow other)
      -- assertFailure
      case e8 of
        Core (CoreCons (ScopedCons
                         (Core (CoreSyntax (Syntax (Stx _ _ (Id "thing")))))
                         (Core (CoreCons
                                 (ScopedCons
                                   expr
                                   (Core (CoreCons (ScopedCons
                                                     (Core (CoreSyntax (Syntax (Stx _ _ (Id "thing")))))
                                                     (Core (CoreEmpty (ScopedEmpty _)))
                                                     _)))
                                   _)))
                         _)) -> assertAlphaEq "the expression is e1" expr e1
        other -> assertFailure ("Expected [vec-syntax [nothing thing ()] thing], got " ++ shortShow other)

    other -> assertFailure ("Expected 8 examples: " ++ show other)


testExpander :: Text -> IO Core -> Assertion
testExpander input spec = do
  output <- spec
  case readExpr "<test suite>" input of
    Left err -> assertFailure . T.unpack $ err
    Right expr -> do
      ctx <- mkInitContext (KernelName kernelName)
      c <- flip execExpand ctx $ do
             initializeKernel
             initializeLanguage (Stx ScopeSet.empty testLoc (KernelName kernelName))
             inEarlierPhase $
               initializeLanguage (Stx ScopeSet.empty testLoc (KernelName kernelName))
             addRootScope expr >>= addModuleScope >>= expandExpr
      case c of
        Left err -> assertFailure . T.unpack . pretty $ err
        Right expanded ->
          case runPartialCore $ unsplit expanded of
            Nothing -> assertFailure "Incomplete expansion"
            Just done -> assertAlphaEq (T.unpack input) output done
  where testLoc = SrcLoc "test contents" (SrcPos 0 0) (SrcPos 0 0)

testExpansionFails :: Text -> (ExpansionErr -> Bool) -> Assertion
testExpansionFails input okp =
  case readExpr "<test suite>" input of
    Left err -> assertFailure . T.unpack $ err
    Right expr -> do
      ctx <- mkInitContext (KernelName kernelName)
      c <- flip execExpand ctx $ do
             initializeKernel
             initializeLanguage (Stx ScopeSet.empty testLoc (KernelName kernelName))
             inEarlierPhase $
               initializeLanguage (Stx ScopeSet.empty testLoc (KernelName kernelName))
             expandExpr =<< addModuleScope =<< addRootScope expr

      case c of
        Left err
          | okp err -> return ()
          | otherwise ->
            assertFailure $ "An error was expected but not this one: " ++ show err
        Right expanded ->
          case runPartialCore $ unsplit expanded of
            Nothing -> assertFailure "Incomplete expansion"
            Just _ -> assertFailure "Error expected, but expansion succeeded"
  where testLoc = SrcLoc "test contents" (SrcPos 0 0) (SrcPos 0 0)


testFile :: FilePath -> (Module [] CompleteDecl -> Assertion) -> Assertion
testFile f p = do
  mn <- moduleNameFromPath f
  ctx <- mkInitContext mn
  void $ execExpand initializeKernel ctx
  execExpand (visit mn >> view expanderWorld <$> getState) ctx >>=
    \case
      Left err -> assertFailure (T.unpack (pretty err))
      Right w ->
        view (worldModules . at mn) w &
        \case
          Nothing ->
            assertFailure "No module found"
          Just (KernelModule _) ->
            assertFailure "Expected user module, got kernel"
          Just (Expanded m) ->
            p m

testFileError :: FilePath -> (ExpansionErr -> Bool) -> Assertion
testFileError f p = do
  mn <- moduleNameFromPath f
  ctx <- mkInitContext mn
  void $ execExpand initializeKernel ctx
  execExpand (visit mn >> view expanderWorld <$> getState) ctx >>=
    \case
      Left err | p err -> return ()
               | otherwise ->
                 assertFailure $ "Expected a different error than " ++
                                 T.unpack (pretty err)
      Right _ -> assertFailure "Unexpected success expanding file"



assertAlphaEq :: (AlphaEq a, ShortShow a) => String -> a -> a -> Assertion
assertAlphaEq preface expected actual =
  unless (alphaEq actual expected) (assertFailure msg)
 where msg = (if null preface then "" else preface ++ "\n") ++
             "expected: " ++ shortShow expected ++ "\n but got: " ++ shortShow actual
