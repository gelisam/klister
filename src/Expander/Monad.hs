{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
import Core
import Env
import Evaluator
import Module
import Phase
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
  = Ready SplitCorePtr Phase Syntax
  | AwaitingSignal SplitCorePtr Signal Value -- the value is the continuation
  | AwaitingMacro SplitCorePtr TaskAwaitMacro
  | ReadyDecl DeclPtr Syntax
  | MoreDecls ModBodyPtr Syntax DeclPtr -- Depends on the binding of the name(s) from the decl

data TaskAwaitMacro = TaskAwaitMacro
  { awaitMacroBinding :: Binding
  , awaitMacroDependsOn :: [SplitCorePtr] -- the [Unique] is the collection of open problems that represent the macro's expansion. When it's empty, the macro is available.
  , awaitMacroLocation :: SplitCorePtr -- the destination into which the macro will be expanded.
  , awaitMacroSyntax :: Syntax -- the syntax object to be expanded once the macro is available
  }

instance Show TaskAwaitMacro where
  show (TaskAwaitMacro _ _ _ stx) = "TaskAwaitMacro " ++ T.unpack (syntaxText stx)

instance Show ExpanderTask where
  show (Ready _dest p stx) = "Ready " ++ show p ++ " " ++ T.unpack (syntaxText stx)
  show (AwaitingSignal _dest on _k) = "AwaitingSignal (" ++ show on ++ ")"
  show (AwaitingMacro _dest t) = "AwaitingMacro (" ++ show t ++ ")"
  show (ReadyDecl _dest stx) = "ReadyDecl " ++ T.unpack (syntaxText stx)
  show (MoreDecls _dest stx _waiting) = "MoreDecls " ++ T.unpack (syntaxText stx)

newtype TaskID = TaskID Unique
  deriving (Eq, Ord)

instance Show TaskID where
  show (TaskID u) = "TaskID " ++ show (hashUnique u)

newTaskID :: Expand TaskID
newTaskID = liftIO $ TaskID <$> newUnique


data ExpansionErr
  = Ambiguous Ident
  | Unknown (Stx Text)
  | NoProgress [ExpanderTask]
  | NotIdentifier Syntax
  | NotEmpty Syntax
  | NotCons Syntax
  | NotList Syntax
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
expansionErrText (Ambiguous x) = "Ambiguous identifier " <> T.pack (show x)
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
  | EPrimDeclMacro (DeclPtr -> Syntax -> Expand ())
  | EVarMacro !Var -- ^ For bound variables (the Unique is the binding site of the var)
  | EUserMacro !SyntacticCategory !Value -- ^ For user-written macros
  | EIncompleteMacro SplitCorePtr -- ^ Macros that are themselves not yet ready to go

data SyntacticCategory = ModuleMacro | DeclMacro | ExprMacro


data ExpanderContext = ExpanderContext
  { _expanderState :: IORef ExpanderState
  , _expanderPhase :: !Phase
  }

mkInitContext :: IO ExpanderContext
mkInitContext = do
  st <- newIORef initExpanderState
  return $ ExpanderContext { _expanderState = st
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
  , _expanderModuleName :: Maybe ModuleName
  , _expanderModuleTop :: Maybe ModBodyPtr
  , _expanderModuleImports :: Imports
  , _expanderModuleExports :: Exports
  , _expanderPhaseRoots :: !(Map Phase Scope)
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
  , _expanderModuleName = Nothing
  , _expanderModuleTop = Nothing
  , _expanderModuleImports = noImports
  , _expanderModuleExports = noExports
  , _expanderPhaseRoots = Map.empty
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


phaseRoot :: Expand Scope
phaseRoot = do
  roots <- view expanderPhaseRoots <$> getState
  p <- currentPhase
  case Map.lookup p roots of
    Just sc -> return sc
    Nothing -> do
      sc <- freshScope
      modifyState $ over (expanderPhaseRoots . at p) $ const (Just sc)
      return sc

makePrisms ''Binding
makePrisms ''ExpansionErr


makePrisms ''EValue
makePrisms ''SyntacticCategory
makePrisms ''ExpansionEnv
makePrisms ''ExpanderTask
