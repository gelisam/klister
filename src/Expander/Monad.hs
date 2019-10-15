{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module Expander.Monad
  ( module Expander.Error
  , module Expander.DeclScope
  -- * The expander monad
  , Expand(..)
  , currentPhase
  , dependencies
  , execExpand
  , freshScope
  , freshVar
  , freshMacroVar
  , getBody
  , getDecl
  , getState
  , inEarlierPhase
  , inPhase
  , linkedCore
  , linkDecl
  , linkExpr
  , modifyState
  , moduleScope
  , newDeclValidityPtr
  , phaseRoot
  , withLocal
  -- ** Context
  , ExpanderContext
  , mkInitContext
  -- ** Tasks
  , module Expander.Task
  , forkAwaitingDefn
  , forkAwaitingMacro
  , forkAwaitingDeclMacro
  , forkAwaitingSignal
  , forkContinueMacroAction
  , forkExpandSyntax
  , forkExpanderTask
  , forkInterpretMacroAction
  , stillStuck
  -- * Implementation parts
  , SyntacticCategory(..)
  , ExpansionEnv(..)
  , EValue(..)
  -- * Expander reader effects
  , ExpanderLocal
  , expanderLocal
  -- ** Lenses
  , expanderPhase
  -- * Expander state
  , ExpanderState
  , expanderState
  -- ** Lenses
  , expanderBindingTable
  , expanderCompletedCore
  , expanderCompletedModBody
  , expanderCurrentEnvs
  , expanderCurrentTransformerEnvs
  , expanderDeclPhases
  , expanderExpansionEnv
  , expanderKernelExports
  , expanderModuleExports
  , expanderModuleImports
  , expanderModuleName
  , expanderModuleTop
  , expanderReceivedSignals
  , expanderTasks
  , expanderWorld
  -- * Tasks
  , TaskID
  , newTaskID
  ) where

import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader
import Data.IORef
import Data.Map (Map)
import Data.Maybe (isJust)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable
import Data.Unique

import Binding
import Control.Lens.IORef
import Core
import Env
import Expander.DeclScope
import Expander.Error
import Expander.Task
import Module
import ModuleName
import PartialCore
import Phase
import Signals
import SplitCore
import Scope
import ScopeCheck.Evidence
import Syntax
import Value
import World

newtype Expand a = Expand
  { runExpand :: ReaderT ExpanderContext (ExceptT ExpansionErr IO) a
  }
  deriving (Functor, Applicative, Monad, MonadError ExpansionErr, MonadIO, MonadReader ExpanderContext)

execExpand :: Expand a -> ExpanderContext -> IO (Either ExpansionErr a)
execExpand act ctx = runExceptT $ runReaderT (runExpand act) ctx

newtype TaskID = TaskID Unique
  deriving (Eq, Ord)

instance Show TaskID where
  show (TaskID u) = "(TaskID " ++ show (hashUnique u) ++ ")"

newTaskID :: Expand TaskID
newTaskID = liftIO $ TaskID <$> newUnique

newDeclValidityPtr :: Expand DeclValidityPtr
newDeclValidityPtr = DeclValidityPtr <$> liftIO newUnique



newtype ExpansionEnv = ExpansionEnv (Map.Map Binding EValue)
  deriving (Semigroup, Monoid)

data EValue
  = EPrimMacro (SplitCorePtr -> Syntax -> Expand ()) -- ^ For "special forms"
  | EPrimModuleMacro (Syntax -> Expand ())
  | EPrimDeclMacro (Scope -> DeclPtr -> DeclValidityPtr -> Syntax -> Expand ())
  | EVarMacro !Var -- ^ For bound variables (the Unique is the binding site of the var)
  | EUserMacro !MacroVar -- ^ For user-written macros
  | EIncompleteMacro !MacroVar !Ident !SplitCorePtr -- ^ Macros that are themselves not yet ready to go
  | EIncompleteDefn !Var !Ident !SplitCorePtr -- ^ Definitions that are not yet ready to go

data SyntacticCategory = ModuleMacro | DeclMacro | ExprMacro


data ExpanderContext = ExpanderContext
  { _expanderLocal :: !ExpanderLocal
  , _expanderState :: IORef ExpanderState
  }

data ExpanderLocal = ExpanderLocal
  { _expanderModuleName :: !ModuleName
  , _expanderPhase :: !Phase
  }

mkInitContext :: ModuleName -> IO ExpanderContext
mkInitContext mn = do
  st <- newIORef initExpanderState
  return $ ExpanderContext { _expanderState = st
                           , _expanderLocal = ExpanderLocal
                             { _expanderModuleName = mn
                             , _expanderPhase = runtime
                             }
                           }

data ExpanderState = ExpanderState
  { _expanderReceivedSignals :: !(Set.Set Signal)
  , _expanderWorld :: !(World Value)
  , _expanderNextScope :: !Scope
  , _expanderBindingTable :: !BindingTable
  , _expanderExpansionEnv :: !ExpansionEnv
  , _expanderTasks :: [(TaskID, ExpanderLocal, ExpanderTask)]
  , _expanderCompletedCore :: !(Map.Map SplitCorePtr (CoreF SplitCorePtr))
  , _expanderCompletedModBody :: !(Map.Map ModBodyPtr (ModuleBodyF DeclPtr ModBodyPtr))
  , _expanderCompletedDecls :: !(Map.Map DeclPtr (Decl DeclPtr SplitCorePtr))
  , _expanderModuleTop :: !(Maybe ModBodyPtr)
  , _expanderModuleImports :: !Imports
  , _expanderModuleExports :: !Exports
  , _expanderPhaseRoots :: !(Map Phase Scope)
  , _expanderModuleRoots :: !(Map ModuleName Scope)
  , _expanderKernelExports :: !Exports
  , _expanderDeclPhases :: !(Map DeclValidityPtr PhaseSpec)
  , _expanderCurrentEnvs :: !(Map Phase (Env Var Value))
  , _expanderCurrentTransformerEnvs :: !(Map Phase (Env MacroVar Value))
  }

initExpanderState :: ExpanderState
initExpanderState = ExpanderState
  { _expanderReceivedSignals = Set.empty
  , _expanderWorld = initialWorld
  , _expanderNextScope = Scope 0
  , _expanderBindingTable = mempty
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
  , _expanderDeclPhases = Map.empty
  , _expanderCurrentEnvs = Map.empty
  , _expanderCurrentTransformerEnvs = Map.empty
  }

makeLenses ''ExpanderContext
makeLenses ''ExpanderLocal
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


withLocal :: ExpanderLocal -> Expand a -> Expand a
withLocal localData = Expand . local (set expanderLocal localData) . runExpand

currentPhase :: Expand Phase
currentPhase = Expand $ view (expanderLocal . expanderPhase) <$> ask

inPhase :: Phase -> Expand a -> Expand a
inPhase p act = Expand $ local (over (expanderLocal . expanderPhase) (const p)) $ runExpand act

inEarlierPhase :: Expand a -> Expand a
inEarlierPhase act =
  Expand $ local (over (expanderLocal . expanderPhase) prior) $ runExpand act

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
  modifyState $ over expanderCompletedCore (<> Map.singleton dest layer)

linkDecl :: DeclPtr -> Decl DeclPtr SplitCorePtr -> Expand ()
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

freshMacroVar :: Expand MacroVar
freshMacroVar = MacroVar <$> liftIO newUnique

stillStuck :: TaskID -> ExpanderTask -> Expand ()
stillStuck tid task = do
  localState <- view expanderLocal
  overIORef expanderState expanderTasks ((tid, localState, task) :)

forkExpanderTask :: ExpanderTask -> Expand ()
forkExpanderTask task = do
  tid <- newTaskID
  localState <- view expanderLocal
  overIORef expanderState expanderTasks ((tid, localState, task) :)

forkExpandSyntax :: MacroDest -> Syntax -> Expand ()
forkExpandSyntax dest stx =
  forkExpanderTask $ ExpandSyntax dest stx

forkAwaitingSignal :: MacroDest -> Signal -> [Closure] -> Expand ()
forkAwaitingSignal dest signal kont =
  forkExpanderTask $ AwaitingSignal dest signal kont

forkAwaitingMacro ::
  Binding -> MacroVar -> Ident -> SplitCorePtr -> SplitCorePtr -> Syntax -> Expand ()
forkAwaitingMacro b v x mdest dest stx =
  forkExpanderTask $ AwaitingMacro (ExprDest dest) (TaskAwaitMacro b v x [mdest] mdest stx)

forkAwaitingDeclMacro ::
  Binding -> MacroVar -> Ident -> SplitCorePtr -> DeclPtr -> Scope -> DeclValidityPtr ->  Syntax -> Expand ()
forkAwaitingDeclMacro b v x mdest dest sc ph stx = do
  forkExpanderTask $ AwaitingMacro (DeclDest dest sc ph) (TaskAwaitMacro b v x [mdest] mdest stx)

forkAwaitingDefn ::
  Var -> Ident -> Binding -> SplitCorePtr ->
  SplitCorePtr -> Syntax ->
  Expand ()
forkAwaitingDefn x n b defn dest stx =
  forkExpanderTask $ AwaitingDefn x n b defn dest stx


forkInterpretMacroAction :: MacroDest -> MacroAction -> [Closure] -> Expand ()
forkInterpretMacroAction dest act kont = do
  forkExpanderTask $ InterpretMacroAction dest act kont

forkContinueMacroAction :: MacroDest -> Value -> [Closure] -> Expand ()
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

getBody :: ModBodyPtr -> Expand [CompleteDecl]
getBody ptr =
  (view (expanderCompletedModBody . at ptr) <$> getState) >>=
  \case
    Nothing -> throwError $ InternalError "Incomplete module after expansion"
    Just Done -> pure []
    Just (Decl decl next) ->
      (:) <$> getDecl decl <*> getBody next

getDecl :: DeclPtr -> Expand CompleteDecl
getDecl ptr =
  (view (expanderCompletedDecls . at ptr) <$> getState) >>=
  \case
    Nothing -> throwError $ InternalError "Missing decl after expansion"
    Just decl -> flattenDecl decl
  where
    flattenDecl :: Decl DeclPtr SplitCorePtr -> Expand (CompleteDecl)
    flattenDecl (Define x v e) =
      linkedCore e >>=
      \case
        Nothing -> throwError $ InternalError "Missing expr after expansion"
        Just e' -> pure $ CompleteDecl $ Define x v e'
    flattenDecl (DefineMacros macros) =
      CompleteDecl . DefineMacros <$>
      for macros \(x, v, e) ->
        linkedCore e >>=
        \case
          Nothing -> throwError $ InternalError "Missing expr after expansion"
          Just e' -> pure $ (x, v, e')
    flattenDecl (Meta d) =
      CompleteDecl . Meta <$> getDecl d
    flattenDecl (Example e) =
      linkedCore e >>=
      \case
        Nothing -> throwError $ InternalError "Missing expr after expansion"
        Just e' -> pure $ CompleteDecl $ Example e'
    flattenDecl (Import spec) = return $ CompleteDecl $ Import spec
    flattenDecl (Export x) = return $ CompleteDecl $ Export x

instance ScopeCheck Expand where
  use phase var = do
    st <- getState
    -- TODO(lb): is this the right check?
    unless (isJust (view (expanderCurrentEnvs . at phase . non Env.empty . at var) st)) $
      fail $ "Var out of scope: " ++ show var -- TODO(lb)

  bindVarIn _ _ _ = undefined -- TODO(lb)
