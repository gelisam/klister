{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Expander.Monad
  ( module Expander.Error
  , module Expander.DeclScope
  -- * The expander monad
  , Expand(..)
  , currentPhase
  , currentBindingLevel
  , inTypeBinder
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
  , isExprChecked
  , linkedCore
  , linkedScheme
  , linkedType
  , linkDecl
  , linkExpr
  , linkType
  , linkScheme
  , modifyState
  , moduleScope
  , newDeclValidityPtr
  , phaseRoot
  , saveExprType
  , trivialScheme
  , withLocal
  , withLocalVarType
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
  , forkExpandType
  , forkTypeCheck
  , forkCheckDecl
  , forkGeneralizeType
  , forkCheckVar
  , forkCompleteTypeCheck
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
  , expanderGlobalBindingTable
  , expanderCompletedCore
  , expanderCompletedDecls
  , expanderCompletedTypes
  , expanderCompletedModBody
  , expanderCompletedSchemes
  , expanderCurrentBindingTable
  , expanderCurrentEnvs
  , expanderCurrentTransformerEnvs
  , expanderDefTypes
  , expanderTypeStore
  , expanderDeclPhases
  , expanderExpansionEnv
  , expanderExpressionTypes
  , expanderKernelBindings
  , expanderKernelExports
  , expanderModuleExports
  , expanderModuleImports
  , expanderModuleName
  , expanderModuleTop
  , expanderReceivedSignals
  , expanderVarTypes
  , expanderTasks
  , expanderWorld
  -- * Tasks
  , TaskID
  , newTaskID
  ) where

import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader
import Data.Foldable
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
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
import PartialType
import Phase
import ShortShow
import Signals
import SplitCore
import SplitType
import Scope
import Syntax
import Type
import Type.Context
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
  | EPrimTypeMacro (SplitTypePtr -> Syntax -> Expand ()) -- ^ For type-level special forms
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
  , _expanderBindingLevels :: !(Map Phase BindingLevel)
  , _expanderVarTypes :: TypeContext Var SchemePtr
  }

mkInitContext :: ModuleName -> IO ExpanderContext
mkInitContext mn = do
  st <- newIORef initExpanderState
  return $ ExpanderContext { _expanderState = st
                           , _expanderLocal = ExpanderLocal
                             { _expanderModuleName = mn
                             , _expanderPhase = runtime
                             , _expanderBindingLevels = Map.empty
                             , _expanderVarTypes = mempty
                             }
                           }

data ExpanderState = ExpanderState
  { _expanderReceivedSignals :: !(Set.Set Signal)
  , _expanderWorld :: !(World Value)
  , _expanderNextScopeNum :: !Int
  , _expanderGlobalBindingTable :: !BindingTable
  , _expanderExpansionEnv :: !ExpansionEnv
  , _expanderTasks :: [(TaskID, ExpanderLocal, ExpanderTask)]
  , _expanderCompletedCore :: !(Map.Map SplitCorePtr (CoreF SplitCorePtr))
  , _expanderCompletedTypes :: !(Map.Map SplitTypePtr (TyF SplitTypePtr))
  , _expanderCompletedModBody :: !(Map.Map ModBodyPtr (ModuleBodyF DeclPtr ModBodyPtr))
  , _expanderCompletedDecls :: !(Map.Map DeclPtr (Decl SchemePtr DeclPtr SplitCorePtr))
  , _expanderModuleTop :: !(Maybe ModBodyPtr)
  , _expanderModuleImports :: !Imports
  , _expanderModuleExports :: !Exports
  , _expanderPhaseRoots :: !(Map Phase Scope)
  , _expanderModuleRoots :: !(Map ModuleName Scope)
  , _expanderKernelBindings :: !BindingTable
  , _expanderKernelExports :: !Exports
  , _expanderDeclPhases :: !(Map DeclValidityPtr PhaseSpec)
  , _expanderCurrentEnvs :: !(Map Phase (Env Var Value))
  , _expanderCurrentTransformerEnvs :: !(Map Phase (Env MacroVar Value))
  , _expanderCurrentBindingTable :: !BindingTable
  , _expanderExpressionTypes :: !(Map SplitCorePtr Ty)
  , _expanderCompletedSchemes :: !(Map SchemePtr (Scheme Ty))
  , _expanderTypeStore :: !(TypeStore Ty)
  , _expanderDefTypes :: !(TypeContext Var SchemePtr) -- ^ Module-level definitions
  }

initExpanderState :: ExpanderState
initExpanderState = ExpanderState
  { _expanderReceivedSignals = Set.empty
  , _expanderWorld = initialWorld
  , _expanderNextScopeNum = 0
  , _expanderGlobalBindingTable = mempty
  , _expanderExpansionEnv = mempty
  , _expanderTasks = []
  , _expanderCompletedCore = Map.empty
  , _expanderCompletedTypes = Map.empty
  , _expanderCompletedModBody = Map.empty
  , _expanderCompletedDecls = Map.empty
  , _expanderModuleTop = Nothing
  , _expanderModuleImports = noImports
  , _expanderModuleExports = noExports
  , _expanderPhaseRoots = Map.empty
  , _expanderModuleRoots = Map.empty
  , _expanderKernelBindings = mempty
  , _expanderKernelExports = noExports
  , _expanderDeclPhases = Map.empty
  , _expanderCurrentEnvs = Map.empty
  , _expanderCurrentTransformerEnvs = Map.empty
  , _expanderCurrentBindingTable = mempty
  , _expanderExpressionTypes = Map.empty
  , _expanderCompletedSchemes = Map.empty
  , _expanderTypeStore = mempty
  , _expanderDefTypes = mempty
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

freshScope :: Text -> Expand Scope
freshScope why = do
  n <- view expanderNextScopeNum <$> getState
  modifyState $ over expanderNextScopeNum $ (+ 1)
  return (Scope n why)


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
      sc <- freshScope $ T.pack $ "Module root for " ++ shortShow mn
      modifyState $ set (expanderModuleRoots . at mn) (Just sc)
      return sc


phaseRoot :: Expand Scope
phaseRoot = do
  roots <- view expanderPhaseRoots <$> getState
  p <- currentPhase
  case Map.lookup p roots of
    Just sc -> return sc
    Nothing -> do
      sc <- freshScope $ T.pack $ "Root for phase " ++ shortShow p
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

linkDecl :: DeclPtr -> Decl SchemePtr DeclPtr SplitCorePtr -> Expand ()
linkDecl dest decl =
  modifyState $ over expanderCompletedDecls $ (<> Map.singleton dest decl)

linkType :: SplitTypePtr -> TyF SplitTypePtr -> Expand ()
linkType dest ty =
  modifyState $ over expanderCompletedTypes (<> Map.singleton dest ty)

linkScheme :: SchemePtr -> Scheme Ty -> Expand ()
linkScheme ptr sch =
  modifyState $ over expanderCompletedSchemes (<> Map.singleton ptr sch)

linkStatus :: SplitCorePtr -> Expand (Maybe (CoreF SplitCorePtr))
linkStatus slot = do
  complete <- view expanderCompletedCore <$> getState
  return $ Map.lookup slot complete

linkedCore :: SplitCorePtr -> Expand (Maybe Core)
linkedCore slot =
  runPartialCore . unsplit . SplitCore slot . view expanderCompletedCore <$>
  getState

linkedType :: SplitTypePtr -> Expand (Maybe Ty)
linkedType slot =
  runPartialType . unsplitType . SplitType slot . view expanderCompletedTypes <$>
  getState

linkedScheme :: SchemePtr -> Expand (Maybe (Scheme Ty))
linkedScheme slot =
  view (expanderCompletedSchemes . at slot) <$> getState

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

forkExpandType :: SplitTypePtr -> Syntax -> Expand ()
forkExpandType dest stx =
  forkExpanderTask $ ExpandSyntax (TypeDest dest) stx

forkCompleteTypeCheck :: SplitCorePtr -> Ty -> Expand ()
forkCompleteTypeCheck eDest ty =
  forkExpanderTask $ TypeCheck eDest (CompleteType ty)

forkTypeCheck :: SplitCorePtr -> SplitTypePtr -> Expand ()
forkTypeCheck eDest ty =
  forkExpanderTask $ TypeCheck eDest (IncompleteType ty)

forkCheckDecl :: DeclPtr -> Expand ()
forkCheckDecl dest =
  forkExpanderTask $ TypeCheckDecl dest

forkGeneralizeType :: SplitCorePtr -> Ty -> SchemePtr -> Expand ()
forkGeneralizeType expr t sch =
  forkExpanderTask $ GeneralizeType expr t sch

forkCheckVar :: SplitCorePtr -> Ty -> Expand ()
forkCheckVar expr ty =
  forkExpanderTask $ TypeCheckVar expr ty

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

-- | Create a "trivial" type scheme that does not generalize any variables
trivialScheme :: Ty -> Expand SchemePtr
trivialScheme t = do
  sch <- liftIO newSchemePtr
  linkScheme sch (Scheme 0 t)
  return sch

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
    flattenDecl ::
      Decl SchemePtr DeclPtr SplitCorePtr ->
      Expand (CompleteDecl)
    flattenDecl (Define x v schPtr e) =
      linkedCore e >>=
      \case
        Nothing -> throwError $ InternalError "Missing expr after expansion"
        Just e' ->
          linkedScheme schPtr >>=
          \case
            Nothing -> throwError $ InternalError "Missing scheme after expansion"
            Just sch -> pure $ CompleteDecl $ Define x v sch e'
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

currentBindingLevel :: Expand BindingLevel
currentBindingLevel = do
  ph <- currentPhase
  view (expanderLocal .
        expanderBindingLevels .
        at ph .
        non topmost)

topmost :: BindingLevel
topmost = BindingLevel 0

inTypeBinder :: Expand a -> Expand a
inTypeBinder act = do
  ph <- currentPhase
  Expand $
    local (over (expanderLocal .
                 expanderBindingLevels .
                 at ph . non topmost) bump) $
    runExpand act
  where
    bump (BindingLevel n) = BindingLevel (n + 1)

withLocalVarType :: Ident -> Var -> SchemePtr -> Expand a -> Expand a
withLocalVarType ident x sch act = do
  ph <- currentPhase
  Expand $
    local (over (expanderLocal . expanderVarTypes . at ph) addVar) $
    runExpand act
  where
    addVar Nothing = Just $ Env.singleton x ident sch
    addVar (Just γ) = Just $ Env.insert x ident sch γ

saveExprType :: SplitCorePtr -> Ty -> Expand ()
saveExprType dest t =
  modifyState $ set (expanderExpressionTypes . at dest) (Just t)

-- | Is the pointed-to expression completely expanded and type checked yet?
isExprChecked :: SplitCorePtr -> Expand Bool
isExprChecked dest = do
  st <- getState
  let found = view (expanderCompletedCore . at dest) st
  case found of
    Nothing -> return False
    Just layer ->
      case view (expanderExpressionTypes . at dest) st of
        Nothing -> return False
        Just _ -> getAll . fold <$> traverse (fmap All . isExprChecked) layer
