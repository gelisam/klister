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
import Control.Monad.Except
import Control.Monad.Reader
import Data.Foldable
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
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

newtype Expand a = Expand
  { runExpand :: ReaderT ExpanderContext (ExceptT ExpansionErr IO) a
  }
  deriving (Functor, Applicative, Monad, MonadError ExpansionErr, MonadIO, MonadReader ExpanderContext)

execExpand :: ExpanderContext -> Expand a -> IO (Either ExpansionErr a)
execExpand ctx act = runExceptT $ runReaderT (runExpand act) ctx


newtype TaskID = TaskID Unique
  deriving (Eq, Ord)

instance Show TaskID where
  show (TaskID u) = "(TaskID " ++ show (hashUnique u) ++ ")"

newTaskID :: Expand TaskID
newTaskID = liftIO $ TaskID <$> newUnique

newDeclOutputScopesPtr :: Expand DeclOutputScopesPtr
newDeclOutputScopesPtr = DeclOutputScopesPtr <$> liftIO newUnique



newtype ExpansionEnv = ExpansionEnv (Map.Map Binding EValue)
  deriving (Semigroup, Monoid)

data EValue
  = EPrimExprMacro (Ty -> SplitCorePtr -> Syntax -> Expand ())
    -- ^ For special forms
  | EPrimTypeMacro (SplitTypePtr -> Syntax -> Expand ()) (TypePatternPtr -> Syntax -> Expand ())
    -- ^ For type-level special forms - first as types, then as type patterns
  | EPrimModuleMacro (Syntax -> Expand ())
  | EPrimDeclMacro (DeclTreePtr -> DeclOutputScopesPtr -> Syntax -> Expand ())
  | EPrimPatternMacro (Either (Ty, Ty, PatternPtr) (Ty, TypePatternPtr) -> Syntax -> Expand ())
  | EPrimUniversalMacro (MacroDest -> Syntax -> Expand ())
  | EVarMacro !Var -- ^ For bound variables (the Unique is the binding site of the var)
  | ETypeVar !Natural -- ^ For bound type variables (user-written Skolem variables or in datatype definitions)
  | EUserMacro !MacroVar -- ^ For user-written macros
  | EIncompleteMacro !MacroVar !Ident !SplitCorePtr -- ^ Macros that are themselves not yet ready to go
  | EIncompleteDefn !Var !Ident !SplitCorePtr -- ^ Definitions that are not yet ready to go
  | EConstructor !Constructor
  -- ^ Constructor identity, elaboration procedure

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
  , _expanderKlisterPath :: !KlisterPath
  , _expanderImportStack :: [ModuleName]
  }

mkInitContext :: ModuleName -> IO ExpanderContext
mkInitContext mn = do
  kPath <- getKlisterPath
  st <- newIORef initExpanderState
  return $ ExpanderContext { _expanderState = st
                           , _expanderLocal = ExpanderLocal
                             { _expanderModuleName = mn
                             , _expanderPhase = runtime
                             , _expanderBindingLevels = Map.empty
                             , _expanderVarTypes = mempty
                             , _expanderKlisterPath = kPath
                             , _expanderImportStack = []
                             }
                           }

data ExpanderState = ExpanderState
  { _expanderWorld :: !(World Value)
  , _expanderNextScopeNum :: !Int
  , _expanderGlobalBindingTable :: !BindingTable
  , _expanderExpansionEnv :: !ExpansionEnv
  , _expanderTasks :: [(TaskID, ExpanderLocal, ExpanderTask)]
  , _expanderOriginLocations :: !(Map.Map SplitCorePtr SrcLoc)
  , _expanderCompletedCore :: !(Map.Map SplitCorePtr (CoreF TypePatternPtr PatternPtr SplitCorePtr))
  , _expanderCompletedPatterns :: !(Map.Map PatternPtr ConstructorPattern)
  , _expanderCompletedTypePatterns :: !(Map.Map TypePatternPtr TypePattern)
  , _expanderPatternBinders :: !(Map.Map (Either PatternPtr TypePatternPtr) [(Scope, Ident, Var, SchemePtr)])
  , _expanderCompletedTypes :: !(Map.Map SplitTypePtr (TyF SplitTypePtr))
  , _expanderCompletedDeclTrees :: !(Map.Map DeclTreePtr (DeclTreeF DeclPtr DeclTreePtr))
  , _expanderCompletedDecls :: !(Map.Map DeclPtr (Decl SplitTypePtr SchemePtr DeclTreePtr SplitCorePtr))
  , _expanderModuleTop :: !(Maybe DeclTreePtr)
  , _expanderModuleImports :: !Imports
  , _expanderModuleExports :: !Exports
  , _expanderPhaseRoots :: !(Map Phase Scope)
  , _expanderModuleRoots :: !(Map ModuleName Scope)
  , _expanderKernelBindings :: !BindingTable
  , _expanderKernelExports :: !Exports
  , _expanderKernelDatatypes :: !(Map Datatype DatatypeInfo)
  , _expanderKernelConstructors :: !(Map Constructor (ConstructorInfo Ty))
  , _expanderKernelValues :: !(Env Var (SchemePtr, Value))
  , _expanderDeclOutputScopes :: !(Map DeclOutputScopesPtr ScopeSet)
  , _expanderCurrentEnvs :: !(Map Phase (Env Var Value))
  , _expanderCurrentTransformerEnvs :: !(Map Phase (Env MacroVar Value))
  , _expanderCurrentDatatypes :: !(Map Phase (Map Datatype DatatypeInfo))
  , _expanderCurrentConstructors :: !(Map Phase (Map Constructor (ConstructorInfo Ty)))
  , _expanderCurrentBindingTable :: !BindingTable
  , _expanderExpressionTypes :: !(Map SplitCorePtr Ty)
  , _expanderCompletedSchemes :: !(Map SchemePtr (Scheme Ty))
  , _expanderTypeStore :: !(TypeStore Ty)
  , _expanderDefTypes :: !(TypeContext Var SchemePtr) -- ^ Module-level definitions
  }

initExpanderState :: ExpanderState
initExpanderState = ExpanderState
  { _expanderWorld = initialWorld
  , _expanderNextScopeNum = 0
  , _expanderGlobalBindingTable = mempty
  , _expanderExpansionEnv = mempty
  , _expanderTasks = []
  , _expanderOriginLocations = Map.empty
  , _expanderCompletedCore = Map.empty
  , _expanderCompletedPatterns = Map.empty
  , _expanderCompletedTypePatterns = Map.empty
  , _expanderPatternBinders = Map.empty
  , _expanderCompletedTypes = Map.empty
  , _expanderCompletedDeclTrees = Map.empty
  , _expanderCompletedDecls = Map.empty
  , _expanderModuleTop = Nothing
  , _expanderModuleImports = noImports
  , _expanderModuleExports = noExports
  , _expanderPhaseRoots = Map.empty
  , _expanderModuleRoots = Map.empty
  , _expanderKernelBindings = mempty
  , _expanderKernelExports = noExports
  , _expanderKernelDatatypes = mempty
  , _expanderKernelConstructors = mempty
  , _expanderKernelValues = mempty
  , _expanderDeclOutputScopes = Map.empty
  , _expanderCurrentEnvs = Map.empty
  , _expanderCurrentTransformerEnvs = Map.empty
  , _expanderCurrentDatatypes = Map.empty
  , _expanderCurrentConstructors = Map.empty
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

linkExpr :: SplitCorePtr -> CoreF TypePatternPtr PatternPtr SplitCorePtr -> Expand ()
linkExpr dest layer =
  modifyState $ over expanderCompletedCore (<> Map.singleton dest layer)

linkPattern :: PatternPtr -> ConstructorPattern -> Expand ()
linkPattern dest pat =
  modifyState $ over expanderCompletedPatterns (<> Map.singleton dest pat)

linkTypePattern :: TypePatternPtr -> TypePattern -> Expand ()
linkTypePattern dest pat =
  modifyState $ over expanderCompletedTypePatterns (<> Map.singleton dest pat)

linkDeclTree :: DeclTreePtr -> DeclTreeF DeclPtr DeclTreePtr -> Expand ()
linkDeclTree dest declTreeF =
  modifyState $ over expanderCompletedDeclTrees $ (<> Map.singleton dest declTreeF)

linkDecl :: DeclPtr -> Decl SplitTypePtr SchemePtr DeclTreePtr SplitCorePtr -> Expand ()
linkDecl dest decl =
  modifyState $ over expanderCompletedDecls $ (<> Map.singleton dest decl)

linkDeclOutputScopes :: DeclOutputScopesPtr -> ScopeSet -> Expand ()
linkDeclOutputScopes dest scopeSet =
  modifyState $ over expanderDeclOutputScopes $ (<> Map.singleton dest scopeSet)

linkOneDecl :: DeclTreePtr -> Decl SplitTypePtr SchemePtr DeclTreePtr SplitCorePtr -> Expand ()
linkOneDecl declTreeDest decl = do
  declDest <- liftIO newDeclPtr
  linkDecl declDest decl
  linkDeclTree declTreeDest (DeclTreeAtom declDest)

linkType :: SplitTypePtr -> TyF SplitTypePtr -> Expand ()
linkType dest ty =
  modifyState $ over expanderCompletedTypes (<> Map.singleton dest ty)

linkScheme :: SchemePtr -> Scheme Ty -> Expand ()
linkScheme ptr sch =
  modifyState $ over expanderCompletedSchemes (<> Map.singleton ptr sch)

linkStatus :: SplitCorePtr -> Expand (Maybe (CoreF TypePatternPtr PatternPtr SplitCorePtr))
linkStatus slot = do
  complete <- view expanderCompletedCore <$> getState
  return $ Map.lookup slot complete

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

forkExpandType :: SplitTypePtr -> Syntax -> Expand ()
forkExpandType dest stx =
  forkExpanderTask $ ExpandSyntax (TypeDest dest) stx


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

getDeclGroup :: DeclTreePtr -> Expand [CompleteDecl]
getDeclGroup ptr =
  (view (expanderCompletedDeclTrees . at ptr) <$> getState) >>=
  \case
    Nothing -> throwError $ InternalError "Incomplete module after expansion"
    Just DeclTreeLeaf -> pure []
    Just (DeclTreeAtom decl) ->
      (:[]) <$> getDecl decl
    Just (DeclTreeBranch l r) ->
      (++) <$> getDeclGroup l <*> getDeclGroup r

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
            Just sch -> pure $ CompleteDecl $ Define x v sch e'
    zonkDecl (DefineMacros macros) =
      CompleteDecl . DefineMacros <$>
      for macros \(x, v, e) ->
        linkedCore e >>=
        \case
          Nothing -> throwError $ InternalError "Missing expr after expansion"
          Just e' -> pure $ (x, v, e')
    zonkDecl (Data x dn arity ctors) =
      CompleteDecl . Data x dn arity <$> traverse zonkCtor ctors
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
            Just sch -> pure $ CompleteDecl $ Example loc sch e'
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
      found <- view (expanderCurrentDatatypes . at ph . non Map.empty . at candidate) <$> getState
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
      found <- view (expanderCurrentConstructors . at ph . non Map.empty . at candidate) <$> getState
      case found of
        Nothing -> return candidate
        Just _ -> go ph mn (Just (maybe 0 (1+) n))

constructorInfo :: Constructor -> Expand (ConstructorInfo Ty)
constructorInfo ctor = do
  p <- currentPhase
  fromWorld <- view (expanderWorld . worldConstructors . at p . non Map.empty . at ctor) <$> getState
  fromModule <- view (expanderCurrentConstructors . at p . non Map.empty . at ctor) <$> getState
  case fromWorld <|> fromModule of
    Nothing ->
      throwError $ InternalError $ "Unknown constructor " ++ show ctor
    Just info -> pure info

datatypeInfo :: Datatype -> Expand DatatypeInfo
datatypeInfo datatype = do
  p <- currentPhase
  fromWorld <- view (expanderWorld . worldDatatypes . at p . non Map.empty . at datatype) <$> getState
  fromModule <- view (expanderCurrentDatatypes . at p . non Map.empty . at datatype) <$> getState
  case fromWorld <|> fromModule of
    Nothing ->
      throwError $ InternalError $ "Unknown datatype " ++ show datatype
    Just info -> pure info

bind :: Binding -> EValue -> Expand ()
bind b v =
  modifyState $
  over expanderExpansionEnv $
  \(ExpansionEnv env) ->
    ExpansionEnv $ Map.insert b v env

-- | Add a binding to the current module's table
addBinding :: Ident -> Binding -> BindingInfo SrcLoc -> Expand ()
addBinding (Stx scs _ name) b info = do
  modifyState $ over (expanderCurrentBindingTable . at name) $
    (Just . ((scs, b, info) :) . fromMaybe [])

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
  return $ addScope' stx sc

-- | Add the current phase's root scope at the current phase
addRootScope :: HasScopes a => a -> Expand a
addRootScope stx = do
  p <- currentPhase
  rsc <- phaseRoot
  return (addScope p stx rsc)

-- | Add the current phase's root scope at all phases (for binding occurrences)
addRootScope' :: HasScopes a => a -> Expand a
addRootScope' stx = do
  rsc <- phaseRoot
  return (addScope' stx rsc)

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
  globalEnv <-  maybe Env.empty id . view (expanderWorld . worldEnvironments . at phase) <$> getState
  localEnv <- maybe Env.empty id . view (expanderCurrentEnvs . at phase) <$> getState
  return (globalEnv <> localEnv)

scheduleType :: Syntax -> Expand SplitTypePtr
scheduleType stx = do
  dest <- liftIO newSplitTypePtr
  forkExpandType dest stx
  return dest

importing :: ModuleName -> Expand a -> Expand a
importing mn act = do
  inProgress <- view (expanderLocal . expanderImportStack) <$> ask
  if mn `elem` inProgress
    then throwError $ CircularImports mn inProgress
    else Expand $ local (over (expanderLocal . expanderImportStack) (mn:)) (runExpand act)
