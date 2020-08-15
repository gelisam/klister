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
import SplitCore
import Syntax.SrcLoc
import Syntax
import Unique
import Value
import World

import Golden

main :: IO ()
main = do
  defaultMain =<< (tests <$> mkGoldenTests)

tests :: TestTree ->TestTree
tests goldenTests = testGroup "All tests"
  [ testGroup "Expander tests" [ operationTests, miniTests, moduleTests ]
  , testGroup "Hedgehog tests" [ testProperty
                                   "runPartialCore . nonPartial = id"
                                   propRunPartialCoreNonPartial
                               , testProperty
                                   "unsplit . split = pure"
                                   propSplitUnsplit
                               ]
  , goldenTests
  ]

operationTests :: TestTree
operationTests =
  testGroup "Core operations"
  [ testCase "Shifting core expressions" $
    let sc = Scope 42 "Test suite"
        scs = ScopeSet.insertAtPhase runtime sc ScopeSet.empty
        stx = Syntax (Stx scs fakeLoc (Id "hey"))
        expr = Core (CoreApp (Core (CoreInteger 2))
                             (Core (CoreSyntax stx)))
    in case shift 1 expr of
         Core (CoreApp (Core (CoreInteger 2))
                       (Core (CoreSyntax stx'))) ->
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
          , int 42
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
              filter (\case {(Example _ _ _) -> True; _ -> False}) &
              \case
                [Example _ _ e1, Example _ _ e2] -> do
                  assertAlphaEq "first example" e1 (Core (corePrimitiveCtor "true" []))
                  assertAlphaEq "second example" e2 (Core (corePrimitiveCtor "false" []))
                _ -> assertFailure "Expected two examples"
          )
        , ( "examples/lang.kl"
          , \m _ ->
              view moduleBody m & map (view completeDecl) &
              \case
                [Define _fn fv _t fbody, Example _ _ e] -> do
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
              filter (\case {(Example _ _ _) -> True; _ -> False}) &
              \case
                [Example _ _ e1, Example _ _ e2] -> do
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
                 Meta [ view completeDecl -> Define _ _ _ _
                      , view completeDecl -> Define _ _ _ _
                      ],
                 DefineMacros [(_, _, _)],
                 Example _ _ ex] ->
                  assertAlphaEq "Example is int" ex (Core (CoreInteger 1))
                _ -> assertFailure "Expected an import, two meta-defs, a macro def, and an example"
          )
        , ( "examples/imports-shifted-macro.kl"
          , \m _ ->
              view moduleBody m & map (view completeDecl) &
              \case
                [Import _, Import _, DefineMacros [(_, _, _)], Example _ _ ex] ->
                  assertAlphaEq "Example is (false)" ex (Core (corePrimitiveCtor "false" []))
                _ -> assertFailure "Expected import, import, macro, example"
          )
        , ( "examples/macro-body-shift.kl"
          , \m _ ->
              view moduleBody m & map (view completeDecl) &
              \case
                [Import _, Define _ _ _ e, DefineMacros [(_, _, _)]] -> do
                  spec <- lam \_x -> lam \y -> lam \_z -> y
                  assertAlphaEq "Definition is λx y z . y" e spec
                _ -> assertFailure "Expected an import, a definition, and a macro"
          )
        , ( "examples/quasiquote.kl"
          , \m _ ->
              view moduleBody m & map (view completeDecl) &
              \case
                (Import _ : Import _ : Meta _ : DefineMacros [_, _] : DefineMacros [_] : Define _ _ _ thingDef : examples) -> do
                  case thingDef of
                    Core (CoreSyntax (Syntax (Stx _ _ (Id "nothing")))) ->
                      case examples of
                        [e1, e2, e3, e4, e5, e6, e7, e8, Example _ _ _, Export _] -> do
                          testQuasiquoteExamples [e1, e2, e3, e4, e5, e6, e7, e8]
                        other -> assertFailure ("Expected 8 tested examples, 1 untested, and 1 export: " ++ show other)
                    other -> assertFailure ("Unexpected thing def " ++ show other)
                _ -> assertFailure "Expected an import, two macros, a definition, and examples"
          )
        , ( "examples/quasiquote-syntax-test.kl"
          , \m _ ->
              view moduleBody m & map (view completeDecl) &
              \case
                (Import _ : Define _ _ _ thingDef : examples) -> do
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
                [Import _, Import _, Define _ fun1 _ firstFun, DefineMacros [_], Define _ fun2 _ secondFun,
                 Example _ _ e1, Example _ _ e2, DefineMacros [_], Example _ _ e3] -> do
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
        , ( "examples/fun-exports.kl"
          , \_m exampleVals ->
              case exampleVals of
                [ValueInteger a, ValueInteger b, ValueInteger c, ValueInteger d] -> do
                  a @?= 1
                  b @?= 2
                  c @?= 3
                  d @?= 4
                _ ->
                  assertFailure "Expected four signals in example"
          )
        , ( "examples/fun-exports-test.kl"
          , \_m exampleVals ->
              case exampleVals of
                [ValueInteger a, ValueInteger b, ValueInteger c] -> do
                  a @?= 1
                  b @?= 2
                  c @?= 3
                _ ->
                  assertFailure "Expected three integers in example"
          )
        , ( "examples/syntax-loc.kl"
          , \_m exampleVals ->
              case exampleVals of
                [ValueSyntax (Syntax (Stx _ loc1 (Id "here"))), ValueSyntax (Syntax (Stx _ loc2 (Id "here")))] -> do
                  let SrcLoc _ (SrcPos l1 c1) (SrcPos l2 c2) = loc1
                      SrcLoc _ (SrcPos l1' c1') (SrcPos l2' c2') = loc2
                  l1  @?= 3
                  c1  @?= 15
                  l2  @?= 3
                  c2  @?= 19
                  l1' @?= 5
                  c1' @?= 16
                  l2' @?= 5
                  c2' @?= 21
                _ ->
                  assertFailure "Expected two identifiers in example"
          )
        , ( "examples/bound-identifier.kl"
          , \_m exampleVals ->
              case exampleVals of
                [ValueSyntax (Syntax (Stx _ _ (Id a))), ValueSyntax (Syntax (Stx _ _ (Id b)))] -> do
                  assertAlphaEq "First example is true" a "t"
                  assertAlphaEq "Second example is false" b "f"
                _ ->
                  assertFailure "Expected two symbols in example"
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
        , ( "examples/non-examples/type-errors.kl"
          , \case
              TypeCheckError (TypeMismatch (Just _) _ _ _) -> True
              _ -> False
          )
        ]
      ]

    isEmpty [] = return ()
    isEmpty _ = assertFailure "Expected empty, got non-empty"

testQuasiquoteExamples :: (Show t, Show sch, Show decl) => [Decl t sch decl Core] -> IO ()
testQuasiquoteExamples examples =
  case examples of
    [ Example _ _ e1, Example _ _ e2, Example _ _ e3, Example _ _ e4,
      Example _ _ e5, Example _ _ e6, Example _ _ e7, Example _ _ e8 ] -> do
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
      c <- execExpand ctx $ completely $ do
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
      c <- execExpand ctx $ completely $ do
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
  void $ execExpand ctx initializeKernel
  (execExpand ctx $ do
    visit mn >> view expanderWorld <$> getState) >>=
    \case
      Left err -> assertFailure (T.unpack (pretty err))
      Right w ->
        view (worldModules . at mn) w &
        \case
          Nothing ->
            assertFailure "No module found"
          Just (KernelModule _) ->
            assertFailure "Expected user module, got kernel"
          Just (Expanded m _) ->
            case Map.lookup mn (view worldEvaluated w) of
              Nothing -> assertFailure "Module values not in its own expansion"
              Just evalResults ->
                p m [val | EvalResult _ _ _ _ val <- evalResults]

testFileError :: FilePath -> (ExpansionErr -> Bool) -> Assertion
testFileError f p = do
  mn <- moduleNameFromPath f
  ctx <- mkInitContext mn
  void $ execExpand ctx initializeKernel
  (execExpand ctx $ do
    visit mn >> view expanderWorld <$> getState) >>=
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

range16 :: Range.Range Int
range16 = Range.linear 0 32

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
genScope = Scope <$> Gen.int range1024 <*> Gen.text range16 Gen.lower

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

genLam ::
  (CoreF TypePattern ConstructorPattern Bool -> GenT IO a) ->
  GenT IO (CoreF TypePattern ConstructorPattern a)
genLam subgen = do
  ident <- Gen.generalize genIdent
  var <- genVar
  CoreLam ident var <$> subgen (CoreLam ident var True)

-- | Generate an instance of 'CoreF'
--
-- Subgenerators have access to both a list of identifiers and the knowledge of
-- which subtree of 'CoreF' they're being asked to generate.
genCoreF ::
  forall a.
  (Maybe (GenT IO Var) -> CoreF TypePattern ConstructorPattern Bool ->
   GenT IO a) {- ^ Generic sub-generator -} ->
  Maybe (GenT IO Var) {- ^ Variable generator -} ->
  GenT IO (CoreF TypePattern ConstructorPattern a)
genCoreF subgen varGen =
  let sameVars = subgen varGen
      -- A unary constructor with no binding
      unary ::
        (forall b. b -> CoreF TypePattern ConstructorPattern b) ->
        GenT IO (CoreF TypePattern ConstructorPattern a)
      unary constructor = constructor <$> sameVars (constructor True)
      -- A binary constructor with no binding
      binary ::
        (forall b. b -> b -> CoreF TypePattern ConstructorPattern b) ->
        GenT IO (CoreF TypePattern ConstructorPattern a)
      binary constructor =
        constructor
        <$> sameVars (constructor True False)
        <*> sameVars (constructor False True)
      -- A ternary constructor with no binding
      ternary ::
        (forall b. b -> b -> b -> CoreF TypePattern ConstructorPattern b) ->
        GenT IO (CoreF TypePattern ConstructorPattern a)
      ternary constructor =
        constructor
        <$> sameVars (constructor True False False)
        <*> sameVars (constructor False True False)
        <*> sameVars (constructor False False True)
      nonRecursive =
        [ (\b -> corePrimitiveCtor (if b then "true" else "false") []) <$> Gen.bool
        , CoreInteger . fromIntegral <$> Gen.int range1024
        ] ++ map (fmap CoreVar) (maybeToList varGen)
      recursive =
        [ genLam sameVars
        , binary CoreApp
        , unary CorePure
        , binary CoreBind
        , CoreSyntaxError <$> genSyntaxError (sameVars (CoreSyntaxError (SyntaxError [] True)))
        -- , CoreIdentEq _ <$> sameVars <*> sameVars
        -- , CoreSyntax Syntax
        -- , CoreCase sameVars [(Pattern, core)]
        -- , CoreIdentifier Ident
        -- , CoreDataCase core [(ConstructorPattern, core)]
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
  let --sub :: Maybe (GenT IO Var) -> CoreF Bool -> GenT IO Core
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
