{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Expander.Monad where

import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader

import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Unique

import Numeric.Natural

import Binding
import Control.Lens.IORef
import Core
import Evaluator
import Module
import ModuleName
import PartialCore
import Phase
import Pretty
import Signals
import SplitCore
import Scope
import ScopeSet (ScopeSet)
import Syntax
import Value
import World

newtype Expand a = Expand
  { runExpand :: ReaderT ExpanderContext (ExceptT ExpansionErr IO) a
  }
  deriving (Functor, Applicative, Monad, MonadError ExpansionErr, MonadIO, MonadReader ExpanderContext)

execExpand :: Expand a -> ExpanderContext -> IO (Either ExpansionErr a)
execExpand act ctx = runExceptT $ runReaderT (runExpand act) ctx


data ExpanderTask
  = ExpandSyntax SplitCorePtr Phase Syntax
  | AwaitingSignal SplitCorePtr Signal [Closure]
  | AwaitingMacro SplitCorePtr TaskAwaitMacro
  | ExpandDecl DeclPtr Scope Syntax
  | ExpandMoreDecls ModBodyPtr Scope Syntax DeclPtr -- Depends on the binding of the name(s) from the decl
  | InterpretMacroAction SplitCorePtr MacroAction [Closure]
  | ContinueMacroAction SplitCorePtr Value [Closure]

data TaskAwaitMacro = TaskAwaitMacro
  { awaitMacroBinding :: Binding
  , awaitMacroDependsOn :: [SplitCorePtr] -- the [Unique] is the collection of open problems that represent the macro's expansion. When it's empty, the macro is available.
  , awaitMacroLocation :: SplitCorePtr -- the destination into which the macro will be expanded.
  , awaitMacroSyntax :: Syntax -- the syntax object to be expanded once the macro is available
  }

instance Show TaskAwaitMacro where
  show (TaskAwaitMacro _ deps _ stx) =
    "(TaskAwaitMacro " ++ show deps ++ " " ++ T.unpack (pretty stx) ++ ")"

instance Show ExpanderTask where
  show (ExpandSyntax _dest p stx) = "ExpandSyntax " ++ show p ++ " " ++ T.unpack (pretty stx)
  show (AwaitingSignal _dest on _k) = "AwaitingSignal (" ++ show on ++ ")"
  show (AwaitingMacro dest t) = "AwaitingMacro (" ++ show dest ++ " " ++ show t ++ ")"
  show (ExpandDecl _dest _sc stx) = "ExpandDecl " ++ T.unpack (syntaxText stx)
  show (ExpandMoreDecls _dest _sc stx _waiting) = "ExpandMoreDecls " ++ T.unpack (syntaxText stx)

newtype TaskID = TaskID Unique
  deriving (Eq, Ord)

instance Show TaskID where
  show (TaskID u) = "TaskID " ++ show (hashUnique u)

newTaskID :: Expand TaskID
newTaskID = liftIO $ TaskID <$> newUnique


data ExpansionErr
  = Ambiguous Phase Ident [ScopeSet]
  | Unknown (Stx Text)
  | NoProgress [ExpanderTask]
  | NotIdentifier Syntax
  | NotEmpty Syntax
  | NotCons Syntax
  | NotList Syntax
  | NotString Syntax
  | NotModName Syntax
  | NotRightLength Natural Syntax
  | NotVec Syntax
  | UnknownPattern Syntax
  | MacroRaisedSyntaxError (SyntaxError Syntax)
  | MacroEvaluationError EvalError
  | ValueNotMacro Value
  | ValueNotSyntax Value
  | InternalError String
  deriving (Show)

expansionErrText :: ExpansionErr -> Text
expansionErrText (Ambiguous p x candidates) =
  "Ambiguous identifier in phase " <> T.pack (show p) <>
  " " <> T.pack (show x) <>
  T.concat ["\n\t" <> T.pack (show c) | c <- candidates]
expansionErrText (Unknown x) = "Unknown: " <> T.pack (show x)
expansionErrText (NoProgress tasks) =
  "No progress was possible: " <> T.pack (show tasks)
expansionErrText (NotIdentifier stx) =
  "Not an identifier: " <> syntaxText stx
expansionErrText (NotEmpty stx) = "Expected (), but got " <> syntaxText stx
expansionErrText (NotCons stx) =
  "Expected non-empty parens, but got " <> syntaxText stx
expansionErrText (NotList stx) =
  "Expected parens, but got " <> syntaxText stx
expansionErrText (NotString stx) =
  "Expected string literal, but got " <> syntaxText stx
expansionErrText (NotModName stx) =
  "Expected module name (string or `kernel'), but got " <> syntaxText stx
expansionErrText (NotRightLength len stx) =
  "Expected " <> T.pack (show len) <>
  " entries between square brackets, but got " <> syntaxText stx
expansionErrText (NotVec stx) =
  "Expected square-bracketed vec but got " <> syntaxText stx
expansionErrText (UnknownPattern stx) =
  "Unknown pattern " <> syntaxText stx
expansionErrText (MacroRaisedSyntaxError err) =
  "Syntax error from macro: " <> T.pack (show err)
expansionErrText (MacroEvaluationError err) =
  "Error during macro evaluation: \n\t" <> evalErrorText err
expansionErrText (ValueNotMacro val) =
  "Not a macro monad value: " <> valueText val
expansionErrText (ValueNotSyntax val) =
  "Not a syntax object: " <> valueText val
expansionErrText (InternalError str) =
  "Internal error during expansion! This is a bug in the implementation." <> T.pack str


type BindingTable = Map Text [(ScopeSet, Binding)]

newtype ExpansionEnv = ExpansionEnv (Map.Map Binding EValue)
  deriving (Semigroup, Monoid)

data EValue
  = EPrimMacro (SplitCorePtr -> Syntax -> Expand ()) -- ^ For "special forms"
  | EPrimModuleMacro (Syntax -> Expand ())
  | EPrimDeclMacro (Scope -> DeclPtr -> Syntax -> Expand ())
  | EVarMacro !Var -- ^ For bound variables (the Unique is the binding site of the var)
  | EUserMacro !SyntacticCategory !Value -- ^ For user-written macros
  | EIncompleteMacro SplitCorePtr -- ^ Macros that are themselves not yet ready to go

data SyntacticCategory = ModuleMacro | DeclMacro | ExprMacro


data ExpanderContext = ExpanderContext
  { _expanderState :: IORef ExpanderState
  , _expanderPhase :: !Phase
  , _expanderModuleName :: !ModuleName
  }

mkInitContext :: ModuleName -> IO ExpanderContext
mkInitContext mn = do
  st <- newIORef initExpanderState
  return $ ExpanderContext { _expanderState = st
                           , _expanderModuleName = mn
                           , _expanderPhase = runtime
                           }

data ExpanderState = ExpanderState
  { _expanderReceivedSignals :: !(Set.Set Signal)
  , _expanderWorld :: !(World Value)
  , _expanderNextScope :: !Scope
  , _expanderBindingTable :: !BindingTable
  , _expanderExpansionEnv :: !ExpansionEnv
  , _expanderTasks :: [(TaskID, ExpanderTask)]
  , _expanderCompletedCore :: !(Map.Map SplitCorePtr (CoreF SplitCorePtr))
  , _expanderCompletedModBody :: !(Map.Map ModBodyPtr (ModuleBodyF DeclPtr ModBodyPtr))
  , _expanderCompletedDecls :: !(Map.Map DeclPtr (Decl SplitCorePtr))
  , _expanderModuleTop :: !(Maybe ModBodyPtr)
  , _expanderModuleImports :: !Imports
  , _expanderModuleExports :: !Exports
  , _expanderPhaseRoots :: !(Map Phase Scope)
  , _expanderModuleRoots :: !(Map ModuleName Scope)
  , _expanderKernelExports :: !Exports
  }

initExpanderState :: ExpanderState
initExpanderState = ExpanderState
  { _expanderReceivedSignals = Set.empty
  , _expanderWorld = initialWorld
  , _expanderNextScope = Scope 0
  , _expanderBindingTable = Map.empty
  , _expanderExpansionEnv = mempty
  , _expanderTasks = []
  , _expanderCompletedCore = Map.empty
  , _expanderCompletedModBody = Map.empty
  , _expanderCompletedDecls = Map.empty
  , _expanderModuleTop = Nothing
  , _expanderModuleImports = noImports
  , _expanderModuleExports = noExports
  , _expanderPhaseRoots = Map.empty
  , _expanderModuleRoots = Map.empty
  , _expanderKernelExports = noExports
  }

makeLenses ''ExpanderContext
makeLenses ''ExpanderState

expanderContext :: Expand ExpanderContext
expanderContext = Expand ask


getState :: Expand ExpanderState
getState = view expanderState <$> expanderContext >>= liftIO . readIORef

modifyState :: (ExpanderState -> ExpanderState) -> Expand ()
modifyState f = do
  st <- view expanderState <$> expanderContext
  liftIO (modifyIORef st f)

freshScope :: Expand Scope
freshScope = do
  sc <- view expanderNextScope <$> getState
  modifyState (\st -> st { _expanderNextScope = nextScope (view expanderNextScope st) })
  return sc


currentPhase :: Expand Phase
currentPhase = Expand $ view expanderPhase <$> ask

inPhase :: Phase -> Expand a -> Expand a
inPhase p act = Expand $ local (over expanderPhase (const p)) $ runExpand act

inEarlierPhase :: Expand a -> Expand a
inEarlierPhase act =
  Expand $ local (over expanderPhase prior) $ runExpand act

moduleScope :: ModuleName -> Expand Scope
moduleScope mn = do
  sc <- moduleScope' mn
  return sc

moduleScope' :: ModuleName -> Expand Scope
moduleScope' mn = do
  mods <- view expanderModuleRoots <$> getState
  case Map.lookup mn mods of
    Just sc -> return sc
    Nothing -> do
      sc <- freshScope
      modifyState $ set (expanderModuleRoots . at mn) (Just sc)
      return sc


phaseRoot :: Expand Scope
phaseRoot = do
  roots <- view expanderPhaseRoots <$> getState
  p <- currentPhase
  case Map.lookup p roots of
    Just sc -> return sc
    Nothing -> do
      sc <- freshScope
      modifyState $ set (expanderPhaseRoots . at p) (Just sc)
      return sc

makePrisms ''Binding
makePrisms ''ExpansionErr
makePrisms ''EValue
makePrisms ''SyntacticCategory
makePrisms ''ExpansionEnv
makePrisms ''ExpanderTask

linkExpr :: SplitCorePtr -> CoreF SplitCorePtr -> Expand ()
linkExpr dest layer =
  modifyState $
  \st -> st { _expanderCompletedCore =
              _expanderCompletedCore st <> Map.singleton dest layer
            }

linkDecl :: DeclPtr -> Decl SplitCorePtr -> Expand ()
linkDecl dest decl =
  modifyState $ over expanderCompletedDecls $ (<> Map.singleton dest decl)

linkStatus :: SplitCorePtr -> Expand (Maybe (CoreF SplitCorePtr))
linkStatus slot = do
  complete <- view expanderCompletedCore <$> getState
  return $ Map.lookup slot complete

linkedCore :: SplitCorePtr -> Expand (Maybe Core)
linkedCore slot =
  runPartialCore . unsplit . SplitCore slot . view expanderCompletedCore <$>
  getState

freshVar :: Expand Var
freshVar = Var <$> liftIO newUnique


forkExpanderTask :: ExpanderTask -> Expand ()
forkExpanderTask task = do
  tid <- newTaskID
  overIORef expanderState expanderTasks ((tid, task) :)

forkExpandSyntax :: SplitCorePtr -> Syntax -> Expand ()
forkExpandSyntax dest stx = do
  p <- currentPhase
  forkExpanderTask $ ExpandSyntax dest p stx

forkAwaitingSignal :: SplitCorePtr -> Signal -> [Closure] -> Expand ()
forkAwaitingSignal dest signal kont = do
  forkExpanderTask $ AwaitingSignal dest signal kont

forkAwaitingMacro :: Binding -> SplitCorePtr -> SplitCorePtr -> Syntax -> Expand ()
forkAwaitingMacro b mdest dest stx = do
  forkExpanderTask $ AwaitingMacro dest (TaskAwaitMacro b [mdest] mdest stx)

forkInterpretMacroAction :: SplitCorePtr -> MacroAction -> [Closure] -> Expand ()
forkInterpretMacroAction dest act kont = do
  forkExpanderTask $ InterpretMacroAction dest act kont

forkContinueMacroAction :: SplitCorePtr -> Value -> [Closure] -> Expand ()
forkContinueMacroAction dest value kont = do
  forkExpanderTask $ ContinueMacroAction dest value kont


-- | Compute the dependencies of a particular slot. The dependencies
-- are the un-linked child slots. If there are no dependencies, then
-- the sub-expression is complete. If the slot is not linked then it
-- depends on itself.
dependencies :: SplitCorePtr -> Expand [SplitCorePtr]
dependencies slot =
  linkStatus slot >>=
  \case
    Nothing -> pure [slot]
    Just c -> foldMap id <$> traverse dependencies c
