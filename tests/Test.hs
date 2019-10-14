{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import Control.Lens hiding (List)
import Control.Monad
import qualified Data.Map as Map
import Control.Monad.IO.Class (liftIO)
import Data.Maybe (maybeToList)
import Data.Text (Text)
import Data.Set (Set)
import qualified Data.Text as T
import Data.Unique (newUnique)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog (testProperty)

import           Hedgehog hiding (eval, Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Hedgehog.Internal.Gen as Gen (generalize)
import qualified Hedgehog.Internal.Property as Prop (forAllT)

import Alpha
import Core
import Core.Builder
import Evaluator (EvalResult(..))
import Expander
import Expander.Monad
import Module
import ModuleName
import Parser
import PartialCore
import Phase (prior, runtime, Phased(..), Phase)
import Pretty
import Scope
import qualified ScopeSet
import ScopeSet (ScopeSet)
import ShortShow
import Signals
import SplitCore
import Syntax.SrcLoc
import Syntax
import Value
import World

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "All tests"
  [ testGroup "Expander tests" [ operationTests, miniTests, moduleTests ]
  , testGroup "Hedgehog tests" [ testProperty
                                   "runPartialCore . nonPartial = id"
                                   propRunPartialCoreNonPartial
                               , testProperty
                                   "unsplit . split = pure"
                                   propSplitUnsplit
                               ]
  ]

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
            \            [[list [_ binder body]] \n\
            \             (syntax-case binder \n\
            \               [[list [x e]] \n\
            \                {- [[lambda [x] body] e] -} \n\
            \                [pure [list-syntax \n\
            \                        [[list-syntax \n\
            \                           [[ident lambda] \n\
            \                            [list-syntax [x] stx] \n\
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
          , \m _ -> isEmpty (view moduleBody m)
          )
        , ( "examples/two-defs.kl"
          , \m _ ->
              view moduleBody m & map (view completeDecl) &
              filter (\case {(Define {}) -> True; _ -> False}) &
              \case
                [Define {}, Define {}] -> pure ()
                _ -> assertFailure "Expected two definitions"
          )
        , ( "examples/id-compare.kl"
          , \m _ ->
              view moduleBody m & map (view completeDecl) &
              filter (\case {(Example _) -> True; _ -> False}) &
              \case
                [Example e1, Example e2] -> do
                  assertAlphaEq "first example" e1 (Core (CoreBool True))
                  assertAlphaEq "second example" e2 (Core (CoreBool False))
                _ -> assertFailure "Expected two examples"
          )
        , ( "examples/lang.kl"
          , \m _ ->
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
          , \m _ ->
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
          , \m _ ->
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
          , \m _ ->
              view moduleBody m & map (view completeDecl) &
              \case
                [Import _, Import _, DefineMacros [(_, _, _)], Example ex] ->
                  assertAlphaEq "Example is #f" ex (Core (CoreBool False))
                _ -> assertFailure "Expected import, import, macro, example"
          )
        , ( "examples/macro-body-shift.kl"
          , \m _ ->
              view moduleBody m & map (view completeDecl) &
              \case
                [Import _, Define _ _ e, DefineMacros [(_, _, _)]] -> do
                  spec <- lam \_x -> lam \y -> lam \_z -> y
                  assertAlphaEq "Definition is λx y z . y" e spec
                _ -> assertFailure "Expected an import, a definition, and a macro"
          )
        , ( "examples/quasiquote.kl"
          , \m _ ->
              view moduleBody m & map (view completeDecl) &
              \case
                (Import _ : Import _ : Meta _ : DefineMacros [_, _] : Define _ _ thingDef : examples) -> do
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
          , \m _ ->
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
        , ( "examples/hygiene.kl"
          , \m _ ->
              view moduleBody m & map (view completeDecl) &
              \case
                [Import _, Import _, Define _ fun1 firstFun, DefineMacros [_], Define _ fun2 secondFun,
                 Example e1, Example e2, DefineMacros [_], Example e3] -> do
                  spec1 <- lam \x -> lam \_y -> x
                  spec2 <- lam \_x -> lam \y -> y
                  assertAlphaEq "First fun drops second argument" firstFun spec1
                  assertAlphaEq "Second fun drops first argument" secondFun spec2
                  case e1 of
                    Core (CoreApp (Core (CoreApp f _)) _) ->
                      assertAlphaEq "Ex 1 picks fun 2" (Core (CoreVar fun2)) f
                    other -> assertFailure $ "Ex 1 should be an application, but it's " ++ shortShow other
                  case e2 of
                    Core (CoreApp (Core (CoreApp f _)) _) ->
                      assertAlphaEq "Ex 2 picks fun 1" (Core (CoreVar fun1)) f
                    other -> assertFailure $ "Ex 2 should be an application, but it's " ++ shortShow other
                  spec3 <- lam (const (pure (Core (CoreVar fun2))))
                  case e3 of
                    Core (CoreApp (Core (CoreApp (Core (CoreApp f _)) _)) _) ->
                      assertAlphaEq "Ex 3 picks fun 2" f spec3
                    other -> assertFailure $ "Ex 3 should be an application, but it's " ++ shortShow other

                _ -> assertFailure "Expected two imports, a def, a macro, a def, two examples, a macro, and an example"
          )
        , ( "examples/defun.kl"
          , \_m exampleVals ->
              case exampleVals of
                [ValueSyntax (Syntax (Stx _ _ (Id "a"))), ValueSyntax (Syntax (Stx _ _ (Id "g")))] ->
                  pure ()
                [_, _] -> assertFailure $ "Wrong example values: " ++ show exampleVals
                _ -> assertFailure "Wrong number of examples in file"
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
        Core (CoreList (ScopedList [Core (CoreSyntax (Syntax (Stx _ _ (Id "thing"))))] _)) -> pure ()
        other -> assertFailure ("Expected (thing), got " ++ shortShow other)
      case e5 of
        Core (CoreList (ScopedList [expr] _)) ->
          assertAlphaEq "the expression is e1" expr e1
        other -> assertFailure ("Expected [nothing], got " ++ shortShow other)
      case e6 of
        Core (CoreList (ScopedList [ Core (CoreSyntax (Syntax (Stx _ _ (Id "list-syntax"))))
                                   , Core (CoreList
                                            (ScopedList [ expr
                                                        , Core (CoreSyntax (Syntax (Stx _ _ (Id "thing"))))
                                                        ]
                                              _))
                                   , _
                                   ]
                        _)) -> assertAlphaEq "the expression is e1" expr e1
        other -> assertFailure ("Expected [list-syntax [nothing thing] thing], got " ++ shortShow other)
      case e7 of
        Core (CoreList (ScopedList [ Core (CoreSyntax (Syntax (Stx _ _ (Id "list-syntax"))))
                                   , Core (CoreList
                                            (ScopedList [ expr
                                                        , Core (CoreSyntax (Syntax (Stx _ _ (Id "thing"))))
                                                        , Core (CoreEmpty _)
                                                        ]
                                              _))
                                   , _
                                   ]
                        _))  -> assertAlphaEq "the expression is e1" expr e1
        other -> assertFailure ("Expected [list-syntax [nothing thing ()] thing], got " ++ shortShow other)
      -- assertFailure
      case e8 of
        Core (CoreList (ScopedList
                         [ Core (CoreSyntax (Syntax (Stx _ _ (Id "thing"))))
                         , expr
                         , Core (CoreSyntax (Syntax (Stx _ _ (Id "thing"))))
                         ]
                         _)) -> assertAlphaEq "the expression is e1" expr e1
        other -> assertFailure ("Expected [thing nothing thing], got " ++ shortShow other)

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


testFile :: FilePath -> (Module [] CompleteDecl -> [Value] -> Assertion) -> Assertion
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
            case Map.lookup mn (view worldEvaluated w) of
              Nothing -> assertFailure "Module valuees not in its own expansion"
              Just evalResults ->
                p m [val | EvalResult _ _ val <- evalResults]

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

--------------------------------------------------------------------------------
-- Hedgehog

-- TODO(lb): Should we be accessing size parameters from the Gen monad to decide
-- these ranges?

range32 :: Range.Range Int
range32 = Range.linear 0 32

range256 :: Range.Range Int
range256 = Range.linear 0 256

range1024 :: Range.Range Int
range1024 = Range.linear 0 1024

genPhase :: MonadGen m => m Phase
genPhase =
  let more 0 phase  = phase
      more n phase = more (n - 1) (prior phase)
  in more <$> Gen.int range256 <*> pure runtime

genScope :: MonadGen m => m Scope
genScope = Scope <$> Gen.int range1024

genSetScope :: MonadGen m => m (Set Scope)
genSetScope = Gen.set range32 genScope

genScopeSet :: MonadGen m => m ScopeSet
genScopeSet =
  let more :: MonadGen m => Int -> ScopeSet -> m ScopeSet
      more 0 ss = pure ss
      more n ss = do
        b <- Gen.choice [pure True, pure False]
        more (n - 1) =<<
          if b
          then ScopeSet.insertAtPhase <$> genPhase <*> genScope <*> pure ss
          else ScopeSet.insertUniversally <$> genScope <*> pure ss
  in flip more ScopeSet.empty =<< Gen.int range256

genSrcPos :: MonadGen m => m SrcPos
genSrcPos = SrcPos <$> Gen.int range256 <*> Gen.int range256

genSrcLoc :: MonadGen m => m SrcLoc
genSrcLoc = SrcLoc <$> Gen.string range256 Gen.ascii <*> genSrcPos <*> genSrcPos

genStx :: MonadGen m => m a -> m (Stx a)
genStx subgen =
  Stx
  <$> genScopeSet
  <*> genSrcLoc
  <*> subgen

genIdent :: MonadGen m => m Ident
genIdent = genStx (Gen.text range256 Gen.ascii)

genVar :: GenT IO Var
genVar = liftIO $ Var <$> newUnique

genSyntaxError :: MonadGen m => m a -> m (SyntaxError a)
genSyntaxError subgen =
  SyntaxError
  <$> Gen.list range256 subgen
  <*> subgen

genLam :: (CoreF Bool -> GenT IO a) -> GenT IO (CoreF a)
genLam subgen = do
  ident <- Gen.generalize genIdent
  var <- genVar
  CoreLam ident var <$> subgen (CoreLam ident var True)

-- | Generate an instance of 'CoreF'
--
-- Subgenerators have access to both a list of identifiers and the knowledge of
-- which subtree of 'CoreF' they're being asked to generate.
genCoreF :: forall a.
  (Maybe (GenT IO Var) -> CoreF Bool -> GenT IO a) {- ^ Generic sub-generator -} ->
  Maybe (GenT IO Var) {- ^ Variable generator -} ->
  GenT IO (CoreF a)
genCoreF subgen varGen =
  let sameVars = subgen varGen
      -- A unary constructor with no binding
      unary :: (forall b. b -> CoreF b) -> GenT IO (CoreF a)
      unary constructor = constructor <$> sameVars (constructor True)
      -- A binary constructor with no binding
      binary :: (forall b. b -> b -> CoreF b) -> GenT IO (CoreF a)
      binary constructor =
        constructor
        <$> sameVars (constructor True False)
        <*> sameVars (constructor False True)
      -- A ternary constructor with no binding
      ternary :: (forall b. b -> b -> b -> CoreF b) -> GenT IO (CoreF a)
      ternary constructor =
        constructor
        <$> sameVars (constructor True False False)
        <*> sameVars (constructor False True False)
        <*> sameVars (constructor False False True)
      nonRecursive =
        [ CoreBool <$> Gen.bool
        , CoreSignal . Signal <$> Gen.int range1024
        ] ++ map (fmap CoreVar) (maybeToList varGen)
      recursive =
        [ genLam sameVars
        , binary CoreApp
        , unary CorePure
        , binary CoreBind
        , CoreSyntaxError <$> genSyntaxError (sameVars (CoreSyntaxError (SyntaxError [] True)))
        , unary CoreSendSignal
        , unary CoreWaitSignal
        -- , CoreIdentEq _ <$> sameVars <*> sameVars
        -- , CoreSyntax Syntax
        -- , CoreCase sameVars [(Pattern, core)]
        -- , CoreIdentifier Ident
        , ternary CoreIf
        -- , CoreIdent (ScopedIdent core)
        -- , CoreEmpty (ScopedEmpty core)
        -- , CoreCons (ScopedCons core)
        -- , CoreVec (ScopedVec core)
        ]
  in Gen.recursive Gen.choice nonRecursive recursive


-- | Generate possibly-ill-scoped 'Core'
genAnyCore :: GenT IO Core
genAnyCore = Core <$> genCoreF (\_varGen _pos -> genAnyCore) (Just genVar)

-- | Generate well-scoped but possibly-ill-formed 'Core'
--
-- e.g. @f a@ where @f@ is not a lambda
genWellScopedCore :: GenT IO Core
genWellScopedCore =
  let sub :: Maybe (GenT IO Var) -> CoreF Bool -> GenT IO Core
      sub vars pos = top $
        case pos of
          CoreLam _ var _ -> Just $ Gen.choice (pure var : maybeToList vars)
          _ -> vars
      top vars = Core <$> genCoreF sub vars
  in top Nothing

propRunPartialCoreNonPartial :: Property
propRunPartialCoreNonPartial = property $ do
  core <- Prop.forAllT $ genAnyCore
  Just core === runPartialCore (nonPartial core)

propSplitUnsplit :: Property
propSplitUnsplit = property $ do
  core <- Prop.forAllT $ genAnyCore
  let part = nonPartial core
  splitted <- liftIO $ split part
  part === unsplit splitted

-- | Test that everything generated by 'genWellFormedCore' can be evaluated
--
-- TODO(lb) this needs to wait for a well-typed 'Core' generator
-- propEvalWellFormed :: Property
-- propEvalWellFormed =
--   property $ do
--     core <- Prop.forAllT $ genWellScopedCore
--     out <- liftIO $ runExceptT $ runReaderT (runEval (eval core)) Env.empty
--     True ===
--       case out of
--         Left _err -> False
--         Right _val -> True
