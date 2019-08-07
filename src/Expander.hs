{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Expander (
  -- * Concrete expanders
    expandModule
  , expandExpr
  -- * Module system
  , visit
  -- * Expander monad
  , Expand
  , execExpand
  , expansionErrText
  , mkInitContext
  , initializeKernel
  , initializeLanguage
  , currentPhase
  , expandEval
  , ExpansionErr(..)
  , ExpanderContext
  , expanderWorld
  , getState
  , addRootScope
  , addModuleScope
  ) where

import Control.Lens hiding (List, children)
import Control.Monad.Except
import Control.Monad.Reader
import Data.Foldable
import Data.List.Extra (maximumOn)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Traversable
import Data.Unique
import System.Directory

import Binding
import Control.Lens.IORef
import Core
import Env
import Evaluator
import Expander.Syntax
import Expander.Monad
import Module
import ModuleName
import Parser
import Phase
import Scope
import ScopeSet (ScopeSet)
import Signals
import SplitCore
import Syntax
import Value
import World
import qualified ScopeSet

expandExpr :: Syntax -> Expand SplitCore
expandExpr stx = do
  dest <- liftIO $ newSplitCorePtr
  forkExpandSyntax dest stx
  expandTasks
  children <- view expanderCompletedCore <$> getState
  return $ SplitCore { _splitCoreRoot = dest
                     , _splitCoreDescendants = children
                     }

initializeLanguage :: Stx ModuleName -> Expand ()
initializeLanguage (Stx scs loc lang) = do
  starters <- visit lang
  forExports_ addModuleBinding starters
  where
    addModuleBinding p n b =
      inPhase p $ do
        ident <- addModuleScope =<< addRootScope' (Stx scs loc n)
        addBinding ident b


expandModule :: ModuleName -> ParsedModule Syntax -> Expand CompleteModule
expandModule thisMod src =
  local (set (expanderLocal . expanderModuleName) thisMod) do
    lang <- mustBeModName (view moduleLanguage src)
    initializeLanguage lang
    modBodyDest <- liftIO $ newModBodyPtr
    modifyState $ set expanderModuleTop $ Just modBodyDest
    decls <- addModuleScope (view moduleContents src)
    forkExpandDecls modBodyDest decls
    expandTasks
    body <- getBody modBodyDest
    let modName = view moduleSource src
    return $ Expanded $ Module
      { _moduleName = modName
      , _moduleImports = noImports
      , _moduleBody = body
      , _moduleExports = noExports
    }
  where
    getBody :: ModBodyPtr -> Expand [CompleteDecl]
    getBody ptr =
      (view (expanderCompletedModBody . at ptr) <$> getState) >>=
      \case
        Nothing -> throwError $ InternalError "Incomplete module after expansion"
        Just Done -> pure []
        Just (Decl decl next) ->
          (:) <$> getDecl decl <*> getBody next
    getDecl ptr =
      (view (expanderCompletedDecls . at ptr) <$> getState) >>=
      \case
        Nothing -> throwError $ InternalError "Missing decl after expansion"
        Just decl -> flatten decl

    flatten :: Decl DeclPtr SplitCorePtr -> Expand (CompleteDecl)
    flatten (Define x v e) =
      linkedCore e >>=
      \case
        Nothing -> throwError $ InternalError "Missing expr after expansion"
        Just e' -> pure $ CompleteDecl $ Define x v e'
    flatten (DefineMacros macros) =
      CompleteDecl . DefineMacros <$>
      for macros \(x, e) ->
        linkedCore e >>=
        \case
          Nothing -> throwError $ InternalError "Missing expr after expansion"
          Just e' -> pure $ (x, e')
    flatten (Meta d) =
      CompleteDecl . Meta <$> getDecl d
    flatten (Example e) =
      linkedCore e >>=
      \case
        Nothing -> throwError $ InternalError "Missing expr after expansion"
        Just e' -> pure $ CompleteDecl $ Example e'
    flatten (Import m x) = return $ CompleteDecl $ Import m x
    flatten (Export x) = return $ CompleteDecl $ Export x




loadModuleFile :: ModuleName -> Expand (CompleteModule, Exports)
loadModuleFile modName =
  case moduleNameToPath modName of
    Right _ ->
      do es <- kernelExports
         p <- currentPhase
         return (KernelModule p, es)
    Left file ->
      do existsp <- liftIO $ doesFileExist file
         when (not existsp) $
           throwError $ InternalError $ "No such file: " ++ show (moduleNameToPath modName)
         stx <- liftIO (readModule file) >>=
                \case
                  Left err -> throwError $ InternalError $ show err -- TODO
                  Right stx -> return stx
         m <- expandModule modName stx
         es <- view expanderModuleExports <$> getState

         modifyState $ over expanderWorld $
            set (worldExports . at modName) (Just es) .
            addExpandedModule m

         return (m, es)


visit :: ModuleName -> Expand Exports
visit modName = do
  (world', m, es) <-
    do world <- view expanderWorld <$> getState
       case view (worldModules . at modName) world of
         Just m -> do
           let es = maybe noExports id (view (worldExports . at modName) world)
           return (world, m, es)
         Nothing -> do
           (m, es) <- loadModuleFile modName
           w <- view expanderWorld <$> getState
           return (w, m, es)
  p <- currentPhase
  let i = phaseNum p
  visitedp <- Set.member p .
              view (expanderWorld . worldVisited . at modName . non Set.empty) <$>
              getState
  if visitedp
    then return ()
    else
        do let m' = shift i m
           let envs = view worldEnvironments world'
           (moreEnvs, _) <- expandEval $ evalMod envs p m'
           modifyState $
             set (expanderWorld . worldVisited . at modName . non Set.empty . at p)
                 (Just ())
           modifyState $ over (expanderWorld . worldEnvironments) (<> moreEnvs)
  return (shift i es)


freshBinding :: Expand Binding
freshBinding = Binding <$> liftIO newUnique

getEValue :: Binding -> Expand EValue
getEValue b = do
  ExpansionEnv env <- view expanderExpansionEnv <$> getState
  case Map.lookup b env of
    Just v -> return v
    Nothing -> throwError (InternalError ("No such binding: " ++ show b))


getTasks :: Expand [(TaskID, ExpanderLocal, ExpanderTask)]
getTasks = view expanderTasks <$> getState

clearTasks :: Expand ()
clearTasks = modifyState $ \st -> st { _expanderTasks = [] }


currentEnv :: Expand (Env Value)
currentEnv = do
  phase <- currentPhase
  globalEnv <- maybe Env.empty id . view (expanderWorld . worldEnvironments . at phase) <$> getState
  localEnv <- maybe Env.empty id . view (expanderCurrentEnvs . at phase) <$> getState
  return (globalEnv <> localEnv)


expandEval :: Eval a -> Expand a
expandEval evalAction = do
  env <- currentEnv
  out <- liftIO $ runExceptT $ runReaderT (runEval evalAction) env
  case out of
    Left err -> do
      p <- currentPhase
      throwError $ MacroEvaluationError p err
    Right val -> return val

bindingTable :: Expand BindingTable
bindingTable = view expanderBindingTable <$> getState

addBinding :: Ident -> Binding -> Expand ()
addBinding (Stx scs _ name) b = do
  -- Note: assumes invariant that a name-scopeset pair is never mapped
  -- to two bindings. That would indicate a bug in the expander but
  -- this code doesn't catch that.
  modifyState $
    \st -> st { _expanderBindingTable =
                Map.insertWith (<>) name [(scs, b)] $
                view expanderBindingTable st
              }

bind :: Binding -> EValue -> Expand ()
bind b v =
  modifyState $
  over expanderExpansionEnv $
  \(ExpansionEnv env) ->
    ExpansionEnv $ Map.insert b v env


allMatchingBindings :: Text -> ScopeSet -> Expand [(ScopeSet, Binding)]
allMatchingBindings x scs = do
  bindings <- bindingTable
  p <- currentPhase
  let namesMatch = fromMaybe [] (Map.lookup x bindings)
  let scopesMatch =
        [ (scopes, b)
        | (scopes, b) <- namesMatch
        , ScopeSet.isSubsetOf p scopes scs
        ]
  return scopesMatch



checkUnambiguous :: ScopeSet -> [ScopeSet] -> Ident -> Expand ()
checkUnambiguous best candidates blame =
  do p <- currentPhase
     let bestSize = ScopeSet.size p best
     let candidateSizes = map (ScopeSet.size p) candidates
     if length (filter (== bestSize) candidateSizes) > 1
       then throwError (Ambiguous p blame candidates)
       else return ()

resolve :: Ident -> Expand Binding
resolve stx@(Stx scs srcLoc x) = do
  p <- currentPhase
  bs <- allMatchingBindings x scs
  case bs of
    [] -> throwError (Unknown (Stx scs srcLoc x))
    candidates ->
      let best = maximumOn (ScopeSet.size p . fst) candidates
      in checkUnambiguous (fst best) (map fst candidates) stx *>
         return (snd best)



resolveImports :: Syntax -> Expand ()
resolveImports _ = pure () -- TODO

buildExports :: Syntax -> Expand ()
buildExports _ = pure ()

kernelExports :: Expand Exports
kernelExports = view expanderKernelExports <$> getState


initializeKernel :: Expand ()
initializeKernel = do
  traverse_ (uncurry addExprPrimitive) exprPrims
  traverse_ (uncurry addModulePrimitive) modPrims
  traverse_ (uncurry addDeclPrimitive) declPrims

  where
    modPrims :: [(Text, Syntax -> Expand ())]
    modPrims =
      [ ( "#%module"
        , \ stx ->
            view expanderModuleTop <$> getState >>=
            \case
              Just _ ->
                error "TODO throw real error - already expanding a module"
              Nothing -> do
                bodyPtr <- liftIO newModBodyPtr
                modifyState $ set expanderModuleTop (Just bodyPtr)
                Stx _ _ (_ :: Syntax, name, imports, body, exports) <- mustBeVec stx
                _actualName <- mustBeIdent name

                resolveImports imports

                forkExpandDecls bodyPtr body

                buildExports exports
                pure ()
        )
      ]

    declPrims :: [(Text, Scope -> DeclPtr -> DeclValidityPtr -> Syntax -> Expand ())]
    declPrims =
      [ ("define"
        , \ sc dest pdest stx -> do
            p <- currentPhase
            Stx _ _ (_, varStx, expr) <- mustBeVec stx
            x <- flip (addScope p) sc <$> mustBeIdent varStx
            b <- freshBinding
            addBinding x b
            var <- freshVar
            exprDest <- liftIO $ newSplitCorePtr
            bind b (EIncompleteDefn var x exprDest)
            linkDecl dest (Define x var exprDest)
            forkExpandSyntax exprDest expr
            nowValidAt pdest p
        )
      ,("define-macros"
        , \ sc dest pdest stx -> do
            Stx _ _ (_ :: Syntax, macroList) <- mustBeVec stx
            Stx _ _ macroDefs <- mustBeList macroList
            p <- currentPhase
            macros <- for macroDefs $ \def -> do
              Stx _ _ (mname, mdef) <- mustBeVec def
              theName <- flip addScope' sc <$> mustBeIdent mname
              b <- freshBinding
              addBinding theName b
              macroDest <- inEarlierPhase $ do
                psc <- phaseRoot
                schedule (addScope p (addScope (prior p) mdef psc) sc)
              bind b $ EIncompleteMacro macroDest
              return (theName, macroDest)
            linkDecl dest $ DefineMacros macros
            nowValidAt pdest p
        )
      , ("example"
        , \ sc dest pdest stx -> do
            p <- currentPhase
            Stx _ _ (_ :: Syntax, expr) <- mustBeVec stx
            exprDest <- liftIO $ newSplitCorePtr
            linkDecl dest (Example exprDest)
            forkExpandSyntax exprDest (addScope p expr sc)
            nowValidAt pdest p
        )
      , ("import" --TODO filename relative to source location of import modname
        , \sc dest pdest stx -> do
            p <- currentPhase
            Stx _ _ (_ :: Syntax, mn, ident) <- mustBeVec stx
            Stx _ _ modName <- mustBeModName mn
            imported@(Stx _ _ x) <- flip (addScope p) sc <$> mustBeIdent ident
            modExports <- visit modName
            b <- case getExport p x modExports of
                   Nothing -> throwError $ InternalError $
                              "Module " ++ show modName ++
                              " does not export " ++ show x ++
                              " amongst " ++ show modExports
                   Just b -> return b
            addBinding imported b
            linkDecl dest (Import modName imported)
            nowValidAt pdest p
        )
      , ("export"
        , \_sc dest pdest stx -> do
            Stx _ _ (_ :: Syntax, ident) <- mustBeVec stx
            exported@(Stx _ _ x) <- mustBeIdent ident
            p <- currentPhase
            b <- resolve exported
            modifyState $ over expanderModuleExports $ addExport p x b
            linkDecl dest (Export exported)
            nowValidAt pdest p
        )
      , ("meta"
        , \sc dest pdest stx -> do
            Stx _ _ (_ :: Syntax, subDecl) <- mustBeVec stx
            subDest <- liftIO newDeclPtr
            linkDecl dest (Meta subDest)
            inEarlierPhase $
              forkExpandOneDecl subDest sc pdest =<< addRootScope subDecl
        )
      ]
      where
        nowValidAt :: DeclValidityPtr -> Phase -> Expand ()
        nowValidAt ptr p =
          modifyState $ over expanderDeclPhases $ Map.insert ptr p


    exprPrims :: [(Text, SplitCorePtr -> Syntax -> Expand ())]
    exprPrims =
      [ ( "oops"
        , \ _ stx -> throwError (InternalError $ "oops" ++ show stx)
        )
      , ( "lambda"
        , \ dest stx -> do
            Stx _ _ (_, arg, body) <- mustBeVec stx
            Stx _ _ theArg <- mustBeVec arg
            (sc, arg', coreArg) <- prepareVar theArg
            p <- currentPhase
            psc <- phaseRoot
            bodyDest <- schedule $ addScope p (addScope p body sc) psc
            linkExpr dest $ CoreLam arg' coreArg bodyDest
        )
      , ( "#%app"
        , \ dest stx -> do
            Stx _ _ (_, fun, arg) <- mustBeVec stx
            funDest <- schedule fun
            argDest <- schedule arg
            linkExpr dest $ CoreApp funDest argDest
        )
      , ( "pure"
        , \ dest stx -> do
            Stx _ _ (_ :: Syntax, v) <- mustBeVec stx
            argDest <- schedule v
            linkExpr dest $ CorePure argDest
        )
      , ( ">>="
        , \ dest stx -> do
            Stx _ _ (_, act, cont) <- mustBeVec stx
            actDest <- schedule act
            contDest <- schedule cont
            linkExpr dest $ CoreBind actDest contDest
        )
      , ( "syntax-error"
        , \dest stx -> do
            Stx scs srcloc (_, args) <- mustBeCons stx
            Stx _ _ (msg, locs) <- mustBeCons $ Syntax $ Stx scs srcloc (List args)
            msgDest <- schedule msg
            locDests <- traverse schedule locs
            linkExpr dest $ CoreSyntaxError (SyntaxError locDests msgDest)
        )
      , ( "send-signal"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, sig) <- mustBeVec stx
            sigDest <- schedule sig
            linkExpr dest $ CoreSendSignal sigDest
        )
      , ( "wait-signal"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, sig) <- mustBeVec stx
            sigDest <- schedule sig
            linkExpr dest $ CoreWaitSignal sigDest
        )
      , ( "bound-identifier=?"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, id1, id2) <- mustBeVec stx
            newE <- CoreIdentEq Bound <$> schedule id1 <*> schedule id2
            linkExpr dest newE
        )
      , ( "free-identifier=?"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, id1, id2) <- mustBeVec stx
            newE <- CoreIdentEq Free <$> schedule id1 <*> schedule id2
            linkExpr dest newE
        )
      , ( "quote"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, quoted) <- mustBeVec stx
            linkExpr dest $ CoreSyntax quoted
        )
      , ( "if"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, b, t, f) <- mustBeVec stx
            linkExpr dest =<< CoreIf <$> schedule b <*> schedule t <*> schedule f
        )
      , ( "ident"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, someId) <- mustBeVec stx
            x@(Stx _ _ _) <- mustBeIdent someId
            linkExpr dest $ CoreIdentifier x
        )
      , ( "ident-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, someId, source) <- mustBeVec stx
            idDest <- schedule someId
            sourceDest <- schedule source
            linkExpr dest $ CoreIdent $ ScopedIdent idDest sourceDest
        )
      , ( "empty-list-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, source) <- mustBeVec stx
            sourceDest <- schedule source
            linkExpr dest $ CoreEmpty $ ScopedEmpty sourceDest
        )
      , ( "cons-list-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, car, cdr, source) <- mustBeVec stx
            carDest <- schedule car
            cdrDest <- schedule cdr
            sourceDest <- schedule source
            linkExpr dest $ CoreCons $ ScopedCons carDest cdrDest sourceDest
        )
      , ( "vec-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, vec, source) <- mustBeVec stx
            Stx _ _ vecItems <- mustBeVec vec
            vecDests <- traverse schedule vecItems
            sourceDest <- schedule source
            linkExpr dest $ CoreVec $ ScopedVec vecDests sourceDest
        )
      , ( "syntax-case"
        , \dest stx -> do
            Stx scs loc (_ :: Syntax, args) <- mustBeCons stx
            Stx _ _ (scrutinee, patterns) <- mustBeCons (Syntax (Stx scs loc (List args)))
            scrutDest <- schedule scrutinee
            patternDests <- traverse (mustBeVec >=> expandPatternCase) patterns
            linkExpr dest $ CoreCase scrutDest patternDests
        )
      , ( "let-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, macro, body) <- mustBeVec stx
            Stx _ _ (mName, mdef) <- mustBeVec macro
            sc <- freshScope
            m <- mustBeIdent mName
            p <- currentPhase
            -- Here, the binding occurrence of the macro gets the
            -- fresh scope at all phases, but later, the scope is only
            -- added to the correct phase in potential use sites.
            -- This prevents the body of the macro (in an earlier
            -- phase) from being able to refer to the macro itself.
            let m' = addScope' m sc
            b <- freshBinding
            addBinding m' b
            macroDest <- inEarlierPhase $ do
              psc <- phaseRoot
              schedule (addScope (prior p) mdef psc)
            forkAwaitingMacro b macroDest dest (addScope p body sc)
        )
      ]

    expandPatternCase :: Stx (Syntax, Syntax) -> Expand (Pattern, SplitCorePtr)
    -- TODO match case keywords hygienically
    expandPatternCase (Stx _ _ (lhs, rhs)) = do
      p <- currentPhase
      case lhs of
        Syntax (Stx _ _ (Vec [Syntax (Stx _ _ (Id "ident")),
                              patVar])) -> do
          (sc, x', var) <- prepareVar patVar
          let rhs' = addScope p rhs sc
          rhsDest <- schedule rhs'
          let patOut = PatternIdentifier x' var
          return (patOut, rhsDest)
        Syntax (Stx _ _ (Vec [Syntax (Stx _ _ (Id "vec")),
                              Syntax (Stx _ _ (Vec vars))])) -> do
          varInfo <- traverse prepareVar vars
          let rhs' = foldr (flip (addScope p)) rhs [sc | (sc, _, _) <- varInfo]
          rhsDest <- schedule rhs'
          let patOut = PatternVec [(ident, var) | (_, ident, var) <- varInfo]
          return (patOut, rhsDest)
        Syntax (Stx _ _ (Vec [Syntax (Stx _ _ (Id "cons")),
                              car,
                              cdr])) -> do
          (sc, car', carVar) <- prepareVar car
          (sc', cdr', cdrVar) <- prepareVar cdr
          let rhs' = addScope p (addScope p rhs sc) sc'
          rhsDest <- schedule rhs'
          let patOut = PatternCons car' carVar cdr' cdrVar
          return (patOut, rhsDest)
        Syntax (Stx _ _ (List [])) -> do
          rhsDest <- schedule rhs
          return (PatternEmpty, rhsDest)
        other ->
          throwError $ UnknownPattern other

    prepareVar :: Syntax -> Expand (Scope, Ident, Var)
    prepareVar varStx = do
      sc <- freshScope
      x <- mustBeIdent varStx
      p <- currentPhase
      psc <- phaseRoot
      let x' = addScope' (addScope p x sc) psc
      b <- freshBinding
      addBinding x' b
      var <- freshVar
      bind b (EVarMacro var)
      return (sc, x', var)


    schedule :: Syntax -> Expand SplitCorePtr
    schedule stx = do
      dest <- liftIO newSplitCorePtr
      forkExpandSyntax dest stx
      return dest

    addToKernel name p b =
      modifyState $ over expanderKernelExports $ addExport p name b

    addModulePrimitive :: Text -> (Syntax -> Expand ()) -> Expand ()
    addModulePrimitive name impl = do
      let val = EPrimModuleMacro impl
      b <- freshBinding
      bind b val
      addToKernel name runtime b

    addDeclPrimitive :: Text -> (Scope -> DeclPtr -> DeclValidityPtr -> Syntax -> Expand ()) -> Expand ()
    addDeclPrimitive name impl = do
      let val = EPrimDeclMacro impl
      b <- freshBinding
      -- FIXME primitive scope:
      bind b val
      addToKernel name runtime b
      when (name == "import") $
        addToKernel name (prior runtime) b


    addExprPrimitive :: Text -> (SplitCorePtr -> Syntax -> Expand ()) -> Expand ()
    addExprPrimitive name impl = do
      let val = EPrimMacro impl
      b <- freshBinding
      bind b val
      addToKernel name runtime b

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


forkExpandOneDecl :: DeclPtr -> Scope -> DeclValidityPtr -> Syntax -> Expand ()
forkExpandOneDecl dest sc phaseDest stx = do
  forkExpanderTask $ ExpandDecl dest sc stx phaseDest

forkExpandDecls :: ModBodyPtr -> Syntax -> Expand ()
forkExpandDecls dest (Syntax (Stx _ _ (List []))) =
  modifyState $
  \st -> st { _expanderCompletedModBody =
              _expanderCompletedModBody st <> Map.singleton dest Done
            }
forkExpandDecls dest (Syntax (Stx scs loc (List (d:ds)))) = do
  -- Create a scope for this new declaration
  sc <- freshScope
  restDest <- liftIO $ newModBodyPtr
  declDest <- liftIO $ newDeclPtr
  declPhase <- newDeclValidityPtr
  modifyState $ over expanderCompletedModBody $
    (<> Map.singleton dest (Decl declDest restDest))
  p <- currentPhase
  forkExpanderTask $
    ExpandMoreDecls restDest sc
      (Syntax (Stx scs loc (List (map (flip (addScope p) sc) ds))))
      declPhase
  forkExpandOneDecl declDest sc declPhase =<< addRootScope d
forkExpandDecls _dest _other =
  error "TODO real error message - malformed module body"


identifierHeaded :: Syntax -> Maybe Ident
identifierHeaded (Syntax (Stx scs srcloc (Id x))) = Just (Stx scs srcloc x)
identifierHeaded (Syntax (Stx _ _ (List (h:_))))
  | (Syntax (Stx scs srcloc (Id x))) <- h = Just (Stx scs srcloc x)
identifierHeaded (Syntax (Stx _ _ (Vec (h:_))))
  | (Syntax (Stx scs srcloc (Id x))) <- h = Just (Stx scs srcloc x)
identifierHeaded _ = Nothing


expandTasks :: Expand ()
expandTasks = do
  tasks <- getTasks
  case tasks of
    [] -> return ()
    more -> do
      clearTasks
      forM_ more runTask
      newTasks <- getTasks
      if taskIDs tasks  == taskIDs newTasks
        then throwError (NoProgress (map (view _3) newTasks))
        else expandTasks
  where
    taskIDs = Set.fromList . map (view _1)

runTask :: (TaskID, ExpanderLocal, ExpanderTask) -> Expand ()
runTask (tid, localState, task) = withLocalState localState $ do
  case task of
    ExpandSyntax dest stx ->
      expandOneExpression dest stx
    AwaitingSignal dest signal kont -> do
      signalWasSent <- viewIORef expanderState (expanderReceivedSignals . at signal)
      case signalWasSent of
        Nothing -> do
          stillStuck tid task
        Just () -> do
          let result = ValueSignal signal  -- TODO: return unit instead
          forkContinueMacroAction dest result kont
    AwaitingMacro dest (TaskAwaitMacro b deps mdest stx) -> do
      newDeps <- concat <$> traverse dependencies deps
      case newDeps of
        (_:_) -> do
          tid' <- if Set.fromList newDeps == Set.fromList deps
                    then return tid
                    else newTaskID
          laterMacro tid' b dest newDeps mdest stx
        [] ->
          linkedCore mdest >>=
          \case
            Nothing -> error "Internal error - macro body not fully expanded"
            Just macroImpl -> do
              macroImplVal <- inEarlierPhase $ expandEval $ eval macroImpl
              bind b $ EUserMacro ExprMacro macroImplVal
              forkExpandSyntax dest stx
    AwaitingDefn x n b defn dest stx ->
      Env.lookupVal x <$> currentEnv >>=
      \case
        Nothing ->
          linkedCore defn >>=
          \case
            Nothing -> stillStuck tid task
            Just e -> do
              p <- currentPhase
              v <- expandEval (eval e)
              let env = Env.singleton x n v
              modifyState $ over (expanderCurrentEnvs . at p) $
                Just . maybe env (<> env)
              bind b $ EVarMacro x
              forkExpandSyntax dest stx
        Just _v -> do
          bind b $ EVarMacro x
          forkExpandSyntax dest stx
    ExpandDecl dest sc stx ph ->
      expandOneDeclaration sc dest stx ph
    ExpandMoreDecls dest sc stx waitingOn -> do
      readyYet <- view (expanderDeclPhases . at waitingOn) <$> getState
      case readyYet of
        Nothing ->
          stillStuck tid task
        Just p -> do
          forkExpandDecls dest (addScope p stx sc)
    InterpretMacroAction dest act outerKont -> do
      interpretMacroAction act >>= \case
        Left (signal, innerKont) -> do
          forkAwaitingSignal dest signal (innerKont ++ outerKont)
        Right value -> do
          forkContinueMacroAction dest value outerKont
    ContinueMacroAction dest value [] -> do
      case value of
        ValueSyntax syntax -> do
          forkExpandSyntax dest syntax
        other -> expandEval $ evalErrorType "syntax" other
    ContinueMacroAction dest value (closure:kont) -> do
      result <- expandEval $ apply closure value
      case result of
        ValueMacroAction macroAction -> do
          forkInterpretMacroAction dest macroAction kont
        other -> expandEval $ evalErrorType "macro action" other
    EvalDefnAction x n p expr ->
      linkedCore expr >>=
      \case
        Nothing -> stillStuck tid task
        Just definiens ->
          inPhase p $ do
            val <- expandEval (eval definiens)
            modifyState $ over (expanderCurrentEnvs . at p) $
              \case
                Nothing -> Just $ Env.singleton x n val
                Just env -> Just $ env <> Env.singleton x n val
  where
    laterMacro tid' b dest deps mdest stx = do
      localConfig <- view expanderLocal
      modifyState $
        over expanderTasks $
          ((tid', localConfig, AwaitingMacro dest (TaskAwaitMacro b deps mdest stx)) :)



expandOneExpression :: SplitCorePtr -> Syntax -> Expand ()
expandOneExpression dest stx
  | Just ident <- identifierHeaded stx = do
      b <- resolve ident
      v <- getEValue b
      case v of
        EPrimMacro impl -> impl dest stx
        EPrimModuleMacro _ ->
          throwError $ InternalError "Current context won't accept modules"
        EPrimDeclMacro _ ->
          throwError $ InternalError "Current context won't accept declarations"
        EVarMacro var ->
          case syntaxE stx of
            Id _ -> linkExpr dest (CoreVar var)
            String _ -> error "Impossible - string not ident"
            Sig _ -> error "Impossible - signal not ident"
            Bool _ -> error "Impossible - boolean not ident"
            List xs -> expandOneExpression dest (addApp List stx xs)
            Vec xs -> expandOneExpression dest (addApp Vec stx xs)
        EIncompleteMacro mdest -> do
          forkAwaitingMacro b mdest dest stx
        EIncompleteDefn x n d ->
          forkAwaitingDefn x n b d dest stx
        EUserMacro ExprMacro (ValueClosure macroImpl) -> do
          stepScope <- freshScope
          p <- currentPhase
          macroVal <- inEarlierPhase $ expandEval $
                      apply macroImpl $
                      ValueSyntax $ addScope p stx stepScope
          case macroVal of
            ValueMacroAction act -> do
              res <- interpretMacroAction act
              case res of
                Left (sig, kont) -> do
                  forkAwaitingSignal dest sig kont
                Right expanded ->
                  case expanded of
                    ValueSyntax expansionResult ->
                      forkExpandSyntax dest (flipScope p expansionResult stepScope)
                    other -> throwError $ ValueNotSyntax other
            other ->
              throwError $ ValueNotMacro other
        EUserMacro _otherCat _otherVal ->
          throwError $ InternalError $ "Invalid macro for expressions"
  | otherwise =
    case syntaxE stx of
      Vec xs -> expandOneExpression dest (addApp Vec stx xs)
      List xs -> expandOneExpression dest (addApp List stx xs)
      Sig s -> expandLiteralSignal dest s
      Bool b -> linkExpr dest (CoreBool b)
      String s -> expandLiteralString dest s
      Id _ -> error "Impossible happened - identifiers are identifier-headed!"

-- | Insert a function application marker with a lexical context from
-- the original expression
addApp :: (forall a . [a] -> ExprF a) -> Syntax -> [Syntax] -> Syntax
addApp ctor (Syntax (Stx scs loc _)) args =
  Syntax (Stx scs loc (ctor (app : args)))
  where
    app = Syntax (Stx scs loc (Id "#%app"))

expandOneDeclaration :: Scope -> DeclPtr -> Syntax -> DeclValidityPtr -> Expand ()
expandOneDeclaration sc dest stx ph
  | Just ident <- identifierHeaded stx = do
      b <- resolve ident
      v <- getEValue b
      case v of
        EPrimMacro _ ->
          throwError $ InternalError "Current context won't accept expressions"
        EPrimModuleMacro _ ->
          throwError $ InternalError "Current context won't accept modules"
        EPrimDeclMacro impl ->
          impl sc dest ph stx
        EVarMacro _ ->
          throwError $ InternalError "Current context won't accept expressions"
        EIncompleteDefn _ _ _ ->
          throwError $ InternalError "Current context won't accept expressions"
        EUserMacro _ _impl ->
          error "Unimplemented: user-defined macros - decl context"
        EIncompleteMacro _ ->
          error "Unimplemented: user-defined macros - decl context - incomplete"
  | otherwise =
    throwError $ InternalError "All declarations should be identifier-headed"


-- | Link the destination to a literal signal object
expandLiteralSignal :: SplitCorePtr -> Signal -> Expand ()
expandLiteralSignal dest signal = linkExpr dest (CoreSignal signal)

expandLiteralString :: SplitCorePtr -> Text -> Expand ()
expandLiteralString _dest str =
  throwError $ InternalError $ "Strings are not valid expressions yet: " ++ show str

-- If we're stuck waiting on a signal, we return that signal and a continuation
-- in the form of a sequence of closures. The first closure should be applied to
-- the result of wait-signal, the second to the result of the first, etc.
interpretMacroAction :: MacroAction -> Expand (Either (Signal, [Closure]) Value)
interpretMacroAction (MacroActionPure value) = do
  pure $ Right value
interpretMacroAction (MacroActionBind macroAction closure) = do
  interpretMacroAction macroAction >>= \case
    Left (signal, closures) -> do
      pure $ Left (signal, closures ++ [closure])
    Right boundResult -> do
      phase <- view (expanderLocal . expanderPhase)
      s <- getState
      let env = fromMaybe Env.empty
              . view (expanderWorld . worldEnvironments . at phase)
              $ s
      evalResult <- liftIO
                  $ runExceptT
                  $ flip runReaderT env
                  $ runEval
                  $ apply closure boundResult
      case evalResult of
        Left evalError -> do
          p <- currentPhase
          throwError $ MacroEvaluationError p evalError
        Right value ->
          case value of
            ValueMacroAction act -> interpretMacroAction act
            other -> throwError $ ValueNotMacro other
interpretMacroAction (MacroActionSyntaxError syntaxError) = do
  throwError $ MacroRaisedSyntaxError syntaxError
interpretMacroAction (MacroActionSendSignal signal) = do
  setIORef expanderState (expanderReceivedSignals . at signal) (Just ())
  pure $ Right $ ValueSignal signal  -- TODO: return unit instead
interpretMacroAction (MacroActionWaitSignal signal) = do
  pure $ Left (signal, [])
interpretMacroAction (MacroActionIdentEq how v1 v2) = do
  id1 <- getIdent v1
  id2 <- getIdent v2
  case how of
    Free -> do
      b1 <- resolve id1
      b2 <- resolve id2
      return $ Right $ ValueBool $ b1 == b2
    Bound -> do
      return $ Right $ ValueBool $ view stxScopeSet id1 == view stxScopeSet id2
  where
    getIdent (ValueSyntax stx) = mustBeIdent stx
    getIdent _other = throwError $ InternalError $ "Not a syntax object in " ++ opName
    opName =
      case how of
        Free  -> "free-identifier=?"
        Bound -> "bound-identifier=?"

