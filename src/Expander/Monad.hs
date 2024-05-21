{-# LANGUAGE BlockArguments     #-}
{-# LANGUAGE CPP                #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE ViewPatterns       #-}
{-# LANGUAGE DerivingStrategies #-}

{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# LANGUAGE BangPatterns #-}

module Expander.Monad
  ( module Expander.Error
  , module Expander.DeclScope
  -- * The expander monad
  , Expand(..)
  , addBinding
  , addImportBinding
  , addDefinedBinding
  , addLocalBinding
  , addRootScope
  , addRootScope'
  , addModuleScope
  , bind
  , completely
  , constructorInfo
  , currentEnv
  , currentPhase
  , klisterPath
  , currentBindingLevel
  , currentTransformerEnv
  , datatypeInfo
  , inTypeBinder
  , dependencies
  , execExpand
  , expandEval
  , freshBinding
  , freshConstructor
  , freshDatatype
  , freshScope
  , freshVar
  , freshMacroVar
  , getDeclGroup
  , getDecl
  , getState
  , inEarlierPhase
  , inLaterPhase
  , inPhase
  , isExprChecked
  , importing
  , kernelExports
  , linkedCore
  , linkedScheme
  , linkedType
  , linkDeclTree
  , linkDecl
  , linkOneDecl
  , linkExpr
  , linkPattern
  , linkTypePattern
  , linkType
  , linkScheme
  , linkDeclOutputScopes
  , modifyState
  , moduleScope
  , newDeclOutputScopesPtr
  , phaseRoot
  , saveExprType
  , saveOrigin
  , trivialScheme
  , withLocal
  , withLocalVarType
  , withLocalVarTypes
  -- ** Context
  , ExpanderContext
  , mkInitContext
  -- ** Tasks
  , module Expander.Task
  , clearTasks
  , getTasks
  , setTasks
  , forkAwaitingDefn
  , forkAwaitingMacro
  , forkAwaitingDeclMacro
  , forkAwaitingTypeCase
  , forkAwaitingType
  , forkContinueMacroAction
  , forkEstablishConstructors
  , forkExpandSyntax
  , forkExpandType
  , forkGeneralizeType
  , forkExpandVar
  , forkExpanderTask
  , forkInterpretMacroAction
  , stillStuck
  , schedule
  , scheduleType
  , scheduleTypeInferKind
  -- * Kinds
  , zonkKind
  -- * Implementation parts
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
  , expanderCompletedPatterns
  , expanderCompletedTypePatterns
  , expanderCompletedDecls
  , expanderCompletedTypes
  , expanderCompletedDeclTrees
  , expanderCompletedSchemes
  , expanderCurrentBindingTable
  , expanderCurrentConstructors
  , expanderCurrentDatatypes
  , expanderCurrentEnvs
  , expanderCurrentTransformerEnvs
  , expanderDefTypes
  , expanderTypeStore
  , expanderKindStore
  , expanderDeclOutputScopes
  , expanderExpansionEnv
  , expanderExpressionTypes
  , expanderKernelBindings
  , expanderKernelExports
  , expanderKernelDatatypes
  , expanderKernelConstructors
  , expanderKernelValues
  , expanderModuleExports
  , expanderModuleImports
  , expanderModuleName
  , expanderModuleTop
  , expanderOriginLocations
  , expanderPatternBinders
  , expanderTypePatternBinders
  , expanderVarTypes
  , expanderTasks
  , expanderWorld
  -- * Tasks
  , TaskID
  , newTaskID
  ) where

import Control.Applicative
import Control.Arrow
import Control.Lens
import Control.Monad
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Except (MonadError(throwError))
import Control.Monad.Reader (MonadReader(ask, local), asks)
import Control.Monad.Trans.Except (ExceptT, runExceptT)
import Control.Monad.Trans.Reader (ReaderT, runReaderT)
import Data.Foldable
import Data.IORef
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Sequence (Seq(..))
import Data.Maybe
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T
import Data.Traversable
import Numeric.Natural

import Binding
import Binding.Info
import Control.Lens.IORef
import Core
import Datatype
import Env
import Evaluator
import Expander.DeclScope
import Expander.Error
import Expander.Task
import Module
import ModuleName
import Kind
import KlisterPath
import PartialCore
import PartialType
import Phase
import ShortShow
import SplitCore
import SplitType
import Scope
import ScopeSet
import Syntax
import Syntax.SrcLoc
import Type
import Type.Context
import Unique
import Value
import World

import Util.Store (Store)
import qualified Util.Store as S
import Util.Key

newtype Expand a = Expand
  { runExpand :: ReaderT ExpanderContext (ExceptT ExpansionErr IO) a
  }
  deriving (Functor, Applicative, Monad, MonadError ExpansionErr, MonadIO, MonadReader ExpanderContext)

execExpand :: ExpanderContext -> Expand a -> IO (Either ExpansionErr a)
execExpand ctx act = runExceptT $ runReaderT (runExpand act) ctx


newtype TaskID = TaskID Unique
  deriving newtype (Eq, Ord, HasKey)

instance Show TaskID where
  show (TaskID u) = "(TaskID " ++ show (hashUnique u) ++ ")"

newTaskID :: Expand TaskID
newTaskID = liftIO $ TaskID <$> newUnique

newDeclOutputScopesPtr :: Expand DeclOutputScopesPtr
newDeclOutputScopesPtr = DeclOutputScopesPtr <$> liftIO newUnique



newtype ExpansionEnv = ExpansionEnv (Store Binding EValue)
  deriving (Semigroup, Monoid)

data EValue
  = EPrimExprMacro (Ty -> SplitCorePtr -> Syntax -> Expand ())
    -- ^ For special forms
  | EPrimTypeMacro (Kind -> SplitTypePtr -> Syntax -> Expand ()) (TypePatternPtr -> Syntax -> Expand ())
    -- ^ For type-level special forms - first as types, then as type patterns
  | EPrimModuleMacro (DeclTreePtr -> Syntax -> Expand ())
  | EPrimDeclMacro (DeclTreePtr -> DeclOutputScopesPtr -> Syntax -> Expand ())
  | EPrimPatternMacro (Ty -> PatternPtr -> Syntax -> Expand ())
  | EPrimTypePatternMacro (TypePatternPtr -> Syntax -> Expand ())
  | EPrimPolyProblemMacro (MacroDest -> Syntax -> Expand ())
  | EVarMacro !Var -- ^ For bound variables (the Unique is the binding site of the var)
  | ETypeVar !Kind !Natural
  -- ^ For bound type variables (user-written Skolem variables or in datatype definitions)
  | EUserMacro !MacroVar -- ^ For user-written macros
  | EIncompleteMacro !MacroVar !Ident !SplitCorePtr -- ^ Macros that are themselves not yet ready to go
  | EIncompleteDefn !Var !Ident !SplitCorePtr -- ^ Definitions that are not yet ready to go
  | EConstructor !Constructor
  -- ^ Constructor identity, elaboration procedure


data ExpanderContext = ExpanderContext
  { _expanderLocal :: !ExpanderLocal
  , _expanderState :: IORef ExpanderState
  }

data ExpanderLocal = ExpanderLocal
  { _expanderModuleName :: !ModuleName
  , _expanderPhase :: !Phase
  , _expanderBindingLevels :: !(Store Phase BindingLevel)
  , _expanderVarTypes :: TypeContext Var SchemePtr
  , _expanderKlisterPath :: !KlisterPath
  , _expanderImportStack :: [ModuleName]
  }

mkInitContext :: ModuleName -> FilePath -> IO ExpanderContext
mkInitContext mn here = do
  kPath <- getKlisterPath
  !st <- newIORef $! initExpanderState here
  return $! ExpanderContext { _expanderState = st
                            , _expanderLocal = ExpanderLocal
                              { _expanderModuleName  = mn
                              , _expanderPhase       = runtime
                              , _expanderBindingLevels = mempty
                              , _expanderVarTypes    = mempty
                              , _expanderKlisterPath = kPath
                              , _expanderImportStack = []
                             }
                           }

data ExpanderState = ExpanderState
  { _expanderWorld              :: !(World Value)
  , _expanderNextScopeNum       :: !Int
  , _expanderGlobalBindingTable :: !BindingTable
  , _expanderExpansionEnv       :: !ExpansionEnv
  , _expanderTasks              :: [(TaskID, ExpanderLocal, ExpanderTask)]
  , _expanderOriginLocations    :: !(Store SplitCorePtr SrcLoc)
  , _expanderCompletedCore      :: !(Store SplitCorePtr (CoreF TypePatternPtr PatternPtr SplitCorePtr))
  , _expanderCompletedPatterns  :: !(Store PatternPtr (ConstructorPatternF PatternPtr))
  , _expanderCompletedTypePatterns :: !(Store TypePatternPtr TypePattern)
  , _expanderPatternBinders     :: !(Store PatternPtr (Either [PatternPtr] (Scope, Ident, Var, SchemePtr)))
  , _expanderTypePatternBinders :: !(Store TypePatternPtr [(Scope, Ident, Var, SchemePtr)])
  , _expanderCompletedTypes     :: !(Store SplitTypePtr (TyF SplitTypePtr))
  , _expanderCompletedDeclTrees :: !(Store DeclTreePtr (DeclTreeF DeclPtr DeclTreePtr))
  , _expanderCompletedDecls     :: !(Store DeclPtr (Decl SplitTypePtr SchemePtr DeclTreePtr SplitCorePtr))
  , _expanderModuleTop          :: !(Maybe DeclTreePtr)
  , _expanderModuleImports      :: !Imports
  , _expanderModuleExports      :: !Exports
  , _expanderPhaseRoots         :: !(Store Phase Scope)
  , _expanderModuleRoots        :: !(HashMap ModuleName Scope)
  , _expanderKernelBindings     :: !BindingTable
  , _expanderKernelExports      :: !Exports
  , _expanderKernelDatatypes    :: !(HashMap Datatype DatatypeInfo)
  , _expanderKernelConstructors :: !(HashMap Constructor (ConstructorInfo Ty))
  , _expanderKernelValues       :: !(Env Var (SchemePtr, Value))
  , _expanderDeclOutputScopes   :: !(Store DeclOutputScopesPtr ScopeSet)
  , _expanderCurrentEnvs        :: !(Store Phase (Env Var Value))
  , _expanderCurrentTransformerEnvs :: !(Store Phase (Env MacroVar Value))
  , _expanderCurrentDatatypes   :: !(Store Phase (HashMap Datatype DatatypeInfo))
  , _expanderCurrentConstructors :: !(Store Phase (HashMap Constructor (ConstructorInfo Ty)))
  , _expanderCurrentBindingTable :: !BindingTable
  , _expanderExpressionTypes    :: !(Store SplitCorePtr Ty)
  , _expanderCompletedSchemes   :: !(Store SchemePtr (Scheme Ty))
  , _expanderTypeStore          :: !(TypeStore Ty)
  , _expanderKindStore          :: !KindStore
  , _expanderDefTypes           :: !(TypeContext Var SchemePtr) -- ^ Module-level definitions
  }

initExpanderState :: FilePath -> ExpanderState
initExpanderState here = ExpanderState
  { _expanderWorld        = initialWorld here
  , _expanderNextScopeNum = 0
  , _expanderGlobalBindingTable = mempty
  , _expanderExpansionEnv       = mempty
  , _expanderTasks              = mempty
  , _expanderOriginLocations    = mempty
  , _expanderCompletedCore      = mempty
  , _expanderCompletedPatterns  = mempty
  , _expanderCompletedTypePatterns = mempty
  , _expanderPatternBinders     = mempty
  , _expanderTypePatternBinders = mempty
  , _expanderCompletedTypes     = mempty
  , _expanderCompletedDeclTrees = mempty
  , _expanderCompletedDecls     = mempty
  , _expanderModuleTop          = Nothing
  , _expanderModuleImports      = noImports
  , _expanderModuleExports      = noExports
  , _expanderPhaseRoots         = mempty
  , _expanderModuleRoots        = mempty
  , _expanderKernelBindings     = mempty
  , _expanderKernelExports      = noExports
  , _expanderKernelDatatypes    = mempty
  , _expanderKernelConstructors = mempty
  , _expanderKernelValues       = mempty
  , _expanderDeclOutputScopes   = mempty
  , _expanderCurrentEnvs        = mempty
  , _expanderCurrentTransformerEnvs = mempty
  , _expanderCurrentDatatypes    = mempty
  , _expanderCurrentConstructors = mempty
  , _expanderCurrentBindingTable = mempty
  , _expanderExpressionTypes     = mempty
  , _expanderCompletedSchemes    = mempty
  , _expanderTypeStore           = mempty
  , _expanderKindStore           = mempty
  , _expanderDefTypes            = mempty
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
  !st <- view expanderState <$> expanderContext
  liftIO (modifyIORef' st f)

#ifndef KDEBUG
freshScope :: Text -> Expand Scope
{-# INLINE freshScope #-}
freshScope _why = do
  n <- view expanderNextScopeNum <$> getState
  modifyState $ over expanderNextScopeNum (+ 1)
  return (Scope n)
#else
freshScope :: Text -> Expand Scope
{-# INLINE freshScope #-}
freshScope why = do
  n <- view expanderNextScopeNum <$> getState
  modifyState $ over expanderNextScopeNum (+ 1)
  return (Scope n why)
#endif

freshBinding :: Expand Binding
freshBinding = Binding <$> liftIO newUnique

withLocal :: ExpanderLocal -> Expand a -> Expand a
withLocal localData = Expand . local (set expanderLocal localData) . runExpand

currentPhase :: Expand Phase
currentPhase = Expand $ view (expanderLocal . expanderPhase) <$> ask

klisterPath :: Expand KlisterPath
klisterPath =
  Expand $ view (expanderLocal . expanderKlisterPath) <$> ask

inPhase :: Phase -> Expand a -> Expand a
inPhase p act = Expand $ local (over (expanderLocal . expanderPhase) (const p)) $ runExpand act

inEarlierPhase :: Expand a -> Expand a
inEarlierPhase act =
  Expand $ local (over (expanderLocal . expanderPhase) prior) $ runExpand act

inLaterPhase :: Expand a -> Expand a
inLaterPhase act =
  Expand $ local (over (expanderLocal . expanderPhase) posterior) $ runExpand act

moduleScope :: ModuleName -> Expand Scope
moduleScope mn = moduleScope' mn

moduleScope' :: ModuleName -> Expand Scope
moduleScope' mn = do
  mods <- view expanderModuleRoots <$> getState
  case HM.lookup mn mods of
    Just sc -> return sc
    Nothing -> do
      sc <- freshScope $ T.pack $ "Module root for " ++ shortShow mn
      modifyState $ set (expanderModuleRoots . at mn) (Just sc)
      return sc


phaseRoot :: Expand Scope
phaseRoot = do
  roots <- view expanderPhaseRoots <$> getState
  p <- currentPhase
  case S.lookup p roots of
    Just sc -> return sc
    Nothing -> do
      sc <- freshScope $ T.pack $ "Root for phase " ++ shortShow p
      modifyState $ set (expanderPhaseRoots . at p) (Just sc)
      return sc

makePrisms ''Binding
makePrisms ''ExpansionErr
makePrisms ''EValue
makePrisms ''ExpansionEnv
makePrisms ''ExpanderTask

linkExpr :: SplitCorePtr -> CoreF TypePatternPtr PatternPtr SplitCorePtr -> Expand ()
linkExpr dest layer =
  modifyState $ over expanderCompletedCore (<> S.singleton dest layer)

linkPattern :: PatternPtr -> ConstructorPatternF PatternPtr -> Expand ()
linkPattern dest pat =
  modifyState $ over expanderCompletedPatterns (<> S.singleton dest pat)

linkTypePattern :: TypePatternPtr -> TypePattern -> [(Scope, Ident, Var, SchemePtr)] -> Expand ()
linkTypePattern dest pat vars = do
  modifyState $ set (expanderTypePatternBinders . at dest) $ Just vars
  modifyState $ over expanderCompletedTypePatterns (<> S.singleton dest pat)

linkDeclTree :: DeclTreePtr -> DeclTreeF DeclPtr DeclTreePtr -> Expand ()
linkDeclTree dest declTreeF =
  modifyState $ over expanderCompletedDeclTrees $ (<> S.singleton dest declTreeF)

linkDecl :: DeclPtr -> Decl SplitTypePtr SchemePtr DeclTreePtr SplitCorePtr -> Expand ()
linkDecl dest decl =
  modifyState $ over expanderCompletedDecls $ (<> S.singleton dest decl)

linkDeclOutputScopes :: DeclOutputScopesPtr -> ScopeSet -> Expand ()
linkDeclOutputScopes dest scopeSet =
  modifyState $ over expanderDeclOutputScopes $ (<> S.singleton dest scopeSet)

linkOneDecl :: DeclTreePtr -> Decl SplitTypePtr SchemePtr DeclTreePtr SplitCorePtr -> Expand ()
linkOneDecl declTreeDest decl = do
  declDest <- liftIO newDeclPtr
  linkDecl declDest decl
  linkDeclTree declTreeDest (DeclTreeAtom declDest)

linkType :: SplitTypePtr -> TyF SplitTypePtr -> Expand ()
linkType dest ty =
  modifyState $ over expanderCompletedTypes (<> S.singleton dest ty)

linkScheme :: SchemePtr -> Scheme Ty -> Expand ()
linkScheme ptr sch =
  modifyState $ over expanderCompletedSchemes (<> S.singleton ptr sch)

linkStatus :: SplitCorePtr -> Expand (Maybe (CoreF TypePatternPtr PatternPtr SplitCorePtr))
linkStatus slot = do
  complete <- view expanderCompletedCore <$> getState
  return $ S.lookup slot complete

linkedCore :: SplitCorePtr -> Expand (Maybe Core)
linkedCore slot =
  runPartialCore . unsplit .
  (\(x, (y, z)) -> SplitCore slot x y z) .
  (view expanderCompletedCore &&& view expanderCompletedPatterns &&& view expanderCompletedTypePatterns) <$>
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

forkAwaitingType :: SplitTypePtr -> [AfterTypeTask] -> Expand ()
forkAwaitingType tdest tasks =
  forkExpanderTask $ AwaitingType tdest tasks

forkExpandType :: Kind -> SplitTypePtr -> Syntax -> Expand ()
forkExpandType kind dest stx =
  forkExpanderTask $ ExpandSyntax (TypeDest kind dest) stx


forkGeneralizeType :: SplitCorePtr -> Ty -> SchemePtr -> Expand ()
forkGeneralizeType expr t sch =
  forkExpanderTask $ GeneralizeType expr t sch

forkExpandVar :: Ty -> SplitCorePtr -> Syntax -> Var -> Expand ()
forkExpandVar ty expr ident var =
  forkExpanderTask $ ExpandVar ty expr ident var

forkAwaitingTypeCase :: SrcLoc -> MacroDest -> Ty -> VEnv -> [(TypePattern, Core)] -> [Closure] -> Expand ()
forkAwaitingTypeCase loc dest ty env cases kont =
  forkExpanderTask $ AwaitingTypeCase loc dest ty env cases kont

forkAwaitingMacro ::
  Binding -> MacroVar -> Ident -> SplitCorePtr -> MacroDest -> Syntax -> Expand ()
forkAwaitingMacro b v x mdest dest stx =
  forkExpanderTask $ AwaitingMacro dest (TaskAwaitMacro b v x [mdest] mdest stx)

forkAwaitingDeclMacro ::
  Binding -> MacroVar -> Ident -> SplitCorePtr -> DeclTreePtr -> DeclOutputScopesPtr -> Syntax -> Expand ()
forkAwaitingDeclMacro b v x mdest dest outScopesDest stx = do
  forkExpanderTask $ AwaitingMacro (DeclTreeDest dest outScopesDest) (TaskAwaitMacro b v x [mdest] mdest stx)

forkAwaitingDefn ::
  Var -> Ident -> Binding -> SplitCorePtr ->
  Ty -> SplitCorePtr -> Syntax ->
  Expand ()
forkAwaitingDefn x n b defn t dest stx =
  forkExpanderTask $ AwaitingDefn x n b defn t dest stx

forkEstablishConstructors ::
  ScopeSet ->
  DeclOutputScopesPtr ->
  Datatype -> [(Ident, Constructor, [SplitTypePtr])] ->
  Expand ()
forkEstablishConstructors scs outScopesDest dt ctors =
  forkExpanderTask $ EstablishConstructors scs outScopesDest dt ctors

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
  linkScheme sch (Scheme [] t)
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

getDeclGroup :: DeclTreePtr -> Expand (Seq CompleteDecl)
getDeclGroup ptr =
  (view (expanderCompletedDeclTrees . at ptr) <$> getState) >>=
  \case
    Nothing -> throwError $ InternalError "Incomplete module after expansion"
    Just DeclTreeLeaf -> pure mempty
    Just (DeclTreeAtom decl) ->
      pure <$> getDecl decl
    Just (DeclTreeBranch l r) ->
      (<>) <$> getDeclGroup l <*> getDeclGroup r

getDecl :: DeclPtr -> Expand CompleteDecl
getDecl ptr =
  (view (expanderCompletedDecls . at ptr) <$> getState) >>=
  \case
    Nothing -> throwError $ InternalError "Missing decl after expansion"
    Just decl -> zonkDecl decl
  where
    zonkDecl ::
      Decl SplitTypePtr SchemePtr DeclTreePtr SplitCorePtr ->
      Expand (CompleteDecl)
    zonkDecl (Define x v schPtr e) =
      linkedCore e >>=
      \case
        Nothing -> throwError $ InternalError "Missing expr after expansion"
        Just e' ->
          linkedScheme schPtr >>=
          \case
            Nothing -> throwError $ InternalError "Missing scheme after expansion"
            Just (Scheme ks t) -> do
              ks' <- traverse zonkKindDefault ks
              pure $ CompleteDecl $ Define x v (Scheme ks' t) e'
    zonkDecl (DefineMacros macros) =
      CompleteDecl . DefineMacros <$>
      for macros \(x, v, e) ->
        linkedCore e >>=
        \case
          Nothing -> throwError $ InternalError "Missing expr after expansion"
          Just e' -> pure $ (x, v, e')
    zonkDecl (Data x dn argKinds ctors) = do
      argKinds' <- traverse zonkKindDefault argKinds
      ctors' <- traverse zonkCtor ctors
      return $ CompleteDecl $ Data x dn argKinds' ctors'
        where
          zonkCtor ::
            (Ident, Constructor, [SplitTypePtr]) ->
            Expand (Ident, Constructor, [Ty])
          zonkCtor (ident, cn, args) = do
            args' <- for args $
                       \ptr' ->
                         linkedType ptr' >>=
                         \case
                           Nothing ->
                             throwError $ InternalError "Missing type after expansion"
                           Just argTy ->
                             pure argTy
            pure (ident, cn, args')
    zonkDecl (Meta d) =
      CompleteDecl . Meta <$> getDeclGroup d
    zonkDecl (Example loc schPtr e) =
      linkedCore e >>=
      \case
        Nothing -> throwError $ InternalError "Missing expr after expansion"
        Just e' ->
          linkedScheme schPtr >>=
          \case
            Nothing -> throwError $ InternalError "Missing example scheme after expansion"
            Just (Scheme ks t) -> do
              ks' <- traverse zonkKindDefault ks
              pure $ CompleteDecl $ Example loc (Scheme ks' t) e'
    zonkDecl (Run loc e) =
      linkedCore e >>=
      \case
        Nothing -> throwError $ InternalError "Missing action after expansion"
        Just e' -> pure $ CompleteDecl $ Run loc e'
    zonkDecl (Import spec) = return $ CompleteDecl $ Import spec
    zonkDecl (Export x) = return $ CompleteDecl $ Export x


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

withLocalVarTypes :: [(Var, Ident, SchemePtr)] -> Expand a -> Expand a
withLocalVarTypes vars act = do
  ph <- currentPhase
  Expand $
    local (over (expanderLocal . expanderVarTypes . at ph) addVars) $
    runExpand act
  where
    addVars Nothing = Just $ Env.fromList vars
    addVars (Just γ) = Just $ γ <> Env.fromList vars

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

saveOrigin :: SplitCorePtr -> SrcLoc -> Expand ()
saveOrigin ptr loc =
  modifyState $ set (expanderOriginLocations . at ptr) (Just loc)

freshDatatype :: Ident -> Expand Datatype
freshDatatype (Stx _ _ hint) = do
  ph <- currentPhase
  mn <- view (expanderLocal . expanderModuleName) <$> ask
  go ph mn Nothing

  where
    go :: Phase -> ModuleName -> Maybe Natural -> Expand Datatype
    go ph mn n = do
      let attempt = hint <> maybe "" (T.pack . show) n
      let candidate = Datatype { _datatypeName = DatatypeName attempt, _datatypeModule = mn }
      found <- view (expanderCurrentDatatypes . at ph . non HM.empty . at candidate) <$> getState
      case found of
        Nothing -> return candidate
        Just _ -> go ph mn (Just (maybe 0 (1+) n))

freshConstructor :: Ident -> Expand Constructor
freshConstructor (Stx _ _ hint) = do
  ph <- currentPhase
  mn <- view (expanderLocal . expanderModuleName) <$> ask
  go ph mn Nothing

  where
    go :: Phase -> ModuleName -> Maybe Natural -> Expand Constructor
    go ph mn n = do
      let attempt = hint <> maybe "" (T.pack . show) n
      let candidate = Constructor { _constructorName = ConstructorName attempt, _constructorModule = mn }
      found <- view (expanderCurrentConstructors . at ph . non HM.empty . at candidate) <$> getState
      case found of
        Nothing -> return candidate
        Just _ -> go ph mn (Just (maybe 0 (1+) n))

constructorInfo :: Constructor -> Expand (ConstructorInfo Ty)
constructorInfo ctor = do
  p <- currentPhase
  fromWorld <- view (expanderWorld . worldConstructors . at p . non mempty . at ctor) <$> getState
  fromModule <- view (expanderCurrentConstructors . at p . non mempty . at ctor) <$> getState
  case fromWorld <|> fromModule of
    Nothing ->
      throwError $ InternalError $ "Unknown constructor " ++ show ctor
    Just info -> pure info

datatypeInfo :: Datatype -> Expand DatatypeInfo
datatypeInfo datatype = do
  p <- currentPhase
  fromWorld <- view (expanderWorld . worldDatatypes . at p . non mempty . at datatype) <$> getState
  fromModule <- view (expanderCurrentDatatypes . at p . non mempty . at datatype) <$> getState
  case fromWorld <|> fromModule of
    Nothing ->
      throwError $ InternalError $ "Unknown datatype " ++ show datatype
    Just info -> pure info

bind :: Binding -> EValue -> Expand ()
bind b v =
  modifyState $
  over expanderExpansionEnv $
  \(ExpansionEnv env) ->
    ExpansionEnv $ S.insert b v env

-- | Add a binding to the current module's table
addBinding :: Ident -> Binding -> BindingInfo SrcLoc -> Expand ()
addBinding (Stx scs _ name) b info = do
  modifyState $ over (expanderCurrentBindingTable . at name) $
    (Just . ((scs, b, info) :<|) . fromMaybe mempty)

addImportBinding :: Ident -> Binding -> Expand ()
addImportBinding x@(Stx _ loc _) b =
  addBinding x b (Imported loc)

addDefinedBinding :: Ident -> Binding -> Expand ()
addDefinedBinding x@(Stx _ loc _) b =
  addBinding x b (Defined loc)

addLocalBinding :: Ident -> Binding -> Expand ()
addLocalBinding x@(Stx _ loc _) b =
  addBinding x b (BoundLocally loc)

addModuleScope :: HasScopes a => a -> Expand a
addModuleScope stx = do
  mn <- view (expanderLocal . expanderModuleName) <$> ask
  sc <- moduleScope mn
  return $ addScope' sc stx

-- | Add the current phase's root scope at the current phase
addRootScope :: HasScopes a => a -> Expand a
addRootScope stx = do
  p <- currentPhase
  rsc <- phaseRoot
  return (addScope p rsc stx)

-- | Add the current phase's root scope at all phases (for binding occurrences)
addRootScope' :: HasScopes a => a -> Expand a
addRootScope' stx = do
  rsc <- phaseRoot
  return (addScope' rsc stx)

-- | Schedule an expression expansion task, returning the pointer to
-- which it will be written.
schedule :: Ty -> Syntax -> Expand SplitCorePtr
schedule t stx@(Syntax (Stx _ loc _)) = do
  dest <- liftIO newSplitCorePtr
  saveOrigin dest loc
  forkExpandSyntax (ExprDest t dest) stx
  return dest

kernelExports :: Expand Exports
kernelExports = view expanderKernelExports <$> getState

completely :: Expand a -> Expand a
completely body = do
  oldTasks <- getTasks
  clearTasks
  a <- body
  remainingTasks <- getTasks
  unless (null remainingTasks) $ do
    throwError (NoProgress (map (view _3) remainingTasks))
  setTasks oldTasks
  pure a

getTasks :: Expand [(TaskID, ExpanderLocal, ExpanderTask)]
getTasks = view expanderTasks <$> getState

setTasks :: [(TaskID, ExpanderLocal, ExpanderTask)] -> Expand ()
setTasks = modifyState . set expanderTasks

clearTasks :: Expand ()
clearTasks = modifyState $ set expanderTasks []

expandEval :: Eval a -> Expand a
expandEval evalAction = do
  env <- currentEnv
  out <- liftIO $ runExceptT $ runReaderT (runEval evalAction) env
  case out of
    Left err -> do
      p <- currentPhase
      throwError $ MacroEvaluationError p err
    Right val -> return val

currentTransformerEnv :: Expand TEnv
currentTransformerEnv = do
  phase <- currentPhase
  globalEnv <- fromMaybe Env.empty . view (expanderWorld . worldTransformerEnvironments . at phase) <$>
               getState
  localEnv <- fromMaybe Env.empty . view (expanderCurrentTransformerEnvs . at phase) <$>
              getState
  return (globalEnv <> localEnv)

currentEnv :: Expand VEnv
currentEnv = do
  phase <- currentPhase
  globalEnv <- fromMaybe mempty . view (expanderWorld . worldEnvironments . at phase) <$> getState
  localEnv  <- fromMaybe mempty . view (expanderCurrentEnvs . at phase) <$> getState
  return $! globalEnv <> localEnv

scheduleType :: Kind -> Syntax -> Expand SplitTypePtr
scheduleType kind stx = do
  dest <- liftIO newSplitTypePtr
  forkExpandType kind dest stx
  return dest


scheduleTypeInferKind :: Syntax -> Expand SplitTypePtr
scheduleTypeInferKind stx = do
  kind <- KMetaVar <$> liftIO newKindVar
  dest <- liftIO newSplitTypePtr
  forkExpandType kind dest stx
  return dest


zonkKind :: Kind -> Expand Kind
zonkKind (KMetaVar v) =
  (view (expanderKindStore . at v) <$> getState) >>=
  \case
    Just k -> zonkKind k
    Nothing -> pure (KMetaVar v)
zonkKind KStar = pure KStar
zonkKind (KFun k1 k2) = KFun <$> zonkKind k1 <*> zonkKind k2

zonkKindDefault :: Kind -> Expand Kind
zonkKindDefault (KMetaVar v) =
  (view (expanderKindStore . at v) <$> getState) >>=
  \case
    Just k -> zonkKindDefault k
    Nothing -> pure KStar
zonkKindDefault KStar = pure KStar
zonkKindDefault (KFun k1 k2) = KFun <$> zonkKindDefault k1 <*> zonkKindDefault k2


importing :: ModuleName -> Expand a -> Expand a
importing mn act = do
  inProgress <- asks (view (expanderLocal . expanderImportStack))
  if mn `elem` inProgress
    then do
    here <- view (expanderWorld . worldLocation) <$> getState
    throwError $
         CircularImports (relativizeModuleName here mn) $
         fmap (relativizeModuleName here) inProgress
    else Expand $ local (over (expanderLocal . expanderImportStack) (mn:)) (runExpand act)
