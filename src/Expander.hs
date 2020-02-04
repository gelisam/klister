{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
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
  , mkInitContext
  , initializeKernel
  , initializeLanguage
  , currentPhase
  , expandEval
  , ExpansionErr(..)
  , ExpanderContext
  , expanderCurrentBindingTable
  , expanderGlobalBindingTable
  , expanderWorld
  , getState
  , addRootScope
  , addModuleScope
  ) where

import Control.Applicative
import Control.Lens hiding (List, children)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Foldable
import Data.List (nub)
import Data.List.Extra (maximumOn)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Traversable
import Data.Unique
import System.Directory

import Binding
import Binding.Info
import Control.Lens.IORef
import Core
import qualified Env
import Evaluator
import Expander.DeclScope
import Expander.Syntax
import Expander.Monad
import Expander.TC
import Module
import ModuleName
import Parser
import Phase
import Pretty
import Scope
import ScopeSet (ScopeSet)
import Signals
import ShortShow
import SplitCore
import SplitType
import Syntax
import Syntax.SrcLoc
import Type
import Value
import World
import qualified ScopeSet

expandExpr :: Syntax -> Expand SplitCore
expandExpr stx = do
  dest <- liftIO $ newSplitCorePtr
  forkExpandSyntax (ExprDest dest) stx
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
        addImportBinding ident b


expandModule :: ModuleName -> ParsedModule Syntax -> Expand CompleteModule
expandModule thisMod src = do
  startBindings <- view expanderCurrentBindingTable <$> getState
  modifyState $ set expanderCurrentBindingTable mempty
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
    let theModule = Module { _moduleName = modName
                           , _moduleImports = noImports
                           , _moduleBody = body
                           , _moduleExports = noExports
                           }
    bs <- view expanderCurrentBindingTable <$> getState
    modifyState $ set expanderCurrentBindingTable startBindings
    return $ Expanded theModule bs




loadModuleFile :: ModuleName -> Expand (CompleteModule, Exports)
loadModuleFile modName =
  case moduleNameToPath modName of
    Right _ ->
      do es <- kernelExports
         p <- currentPhase
         return (KernelModule p, es)
    Left file ->
      do existsp <- liftIO $ doesFileExist file
         when (not existsp) $ throwError $ NoSuchFile $ show file
         stx <- liftIO (readModule file) >>=
                \case
                  Left err -> throwError $ ReaderError err
                  Right stx -> return stx
         m <- expandModule modName stx
         es <- view expanderModuleExports <$> getState

         modifyState $ over expanderWorld $
            set (worldExports . at modName) (Just es) .
            addExpandedModule m

         return (m, es)

getExports :: ExportSpec -> Expand Exports
getExports (ExportIdents idents) = do
  p <- currentPhase
  bs <- for idents $ \x -> do
    x' <- addRootScope' x
    binding <- resolve x'
    return (view stxValue x, binding)
  return $ foldr (uncurry $ addExport p) noExports bs
getExports (ExportRenamed spec rens) = mapExportNames rename <$> getExports spec
  where
    rename x =
      case lookup x rens of
        Nothing -> x
        Just y -> y
getExports (ExportPrefixed spec pref) = mapExportNames (pref <>) <$> getExports spec
getExports (ExportShifted spec i) = do
  p <- currentPhase
  inPhase (shift i p) $
    getExports spec

getImports :: ImportSpec -> Expand Exports
getImports (ImportModule (Stx _ _ mn)) = visit mn
getImports (ImportOnly spec idents) = do
  imports <- getImports spec
  p <- currentPhase
  -- Check that all the identifiers are actually exported
  for_ idents $ \x ->
    case getExport p (view stxValue x) imports of
      Nothing -> throwError $ NotExported x p
      Just _ -> pure ()
  return $ filterExports (\_ x -> x `elem` (map (view stxValue) idents)) imports
getImports (ShiftImports spec i) = do
  p <- currentPhase
  inPhase (shift i p) $ getImports spec
getImports (RenameImports spec (map (bimap (view stxValue) (view stxValue)) -> rens)) =
  mapExportNames rename <$> getImports spec
  where
    rename x =
      case lookup x rens of
        Nothing -> x
        Just y -> y
getImports (PrefixImports spec pref) =
  mapExportNames (pref <>) <$> getImports spec

visit :: ModuleName -> Expand Exports
visit modName = do
  (m, es) <-
    do world <- view expanderWorld <$> getState
       case view (worldModules . at modName) world of
         Just m -> do
           let es = maybe noExports id (view (worldExports . at modName) world)
           return (m, es)
         Nothing ->
           inPhase runtime $
             loadModuleFile modName
  p <- currentPhase
  let i = phaseNum p
  visitedp <- Set.member p .
              view (expanderWorld . worldVisited . at modName . non Set.empty) <$>
              getState
  unless visitedp $ do
    let m' = shift i m -- Shift the syntax literals in the module source code
    evalResults <- inPhase p $ evalMod m'
    modifyState $
      set (expanderWorld . worldEvaluated . at modName)
          (Just evalResults)
    let bs = getModuleBindings m'
    modifyState $ over expanderGlobalBindingTable $ (<> bs)
  return (shift i es)
  where getModuleBindings (Expanded _ bs) = bs
        getModuleBindings (KernelModule _) = mempty

-- | Evaluate an expanded module at the current expansion phase,
-- recursively loading its run-time dependencies.
evalMod :: CompleteModule -> Expand [EvalResult]
evalMod (KernelModule _) =
  -- Builtins go here, suitably shifted. There are no built-in values
  -- yet, only built-in syntax, but this may change.
  return []
evalMod (Expanded em _) = snd <$> runWriterT (traverse_ evalDecl (view moduleBody em))
  where
    evalDecl (CompleteDecl d) =
      case d of
        Define x n sch e -> do
          val <- lift $ expandEval (eval e)
          p <- lift currentPhase
          -- TODO save sch here
          lift $ modifyState $
            over (expanderWorld . worldEnvironments . at p . non Env.empty) $
              Env.insert n x val
        Example expr -> do
          env <- lift currentEnv
          value <- lift $ expandEval (eval expr)
          tell $ [EvalResult { resultEnv = env
                             , resultExpr = expr
                             , resultValue = value
                             }]

        DefineMacros macros -> do
          p <- lift currentPhase
          lift $ inEarlierPhase $ for_ macros $ \(x, n, e) -> do
            v <- expandEval (eval e)
            modifyState $
              over (expanderWorld . worldTransformerEnvironments . at p . non Env.empty) $
                Env.insert n x v
        Meta decl -> do
          ((), out) <- lift $ inEarlierPhase (runWriterT $ evalDecl decl)
          tell out
        Import spec -> lift $ getImports spec >> pure () -- for side effect of evaluating module
        Export _ -> pure ()

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
clearTasks = modifyState $ set expanderTasks []

currentTransformerEnv :: Expand TEnv
currentTransformerEnv = do
  phase <- currentPhase
  globalEnv <- view (expanderWorld . worldTransformerEnvironments . at phase . non Env.empty) <$>
               getState
  localEnv <- view (expanderCurrentTransformerEnvs . at phase . non Env.empty) <$>
              getState
  return (globalEnv <> localEnv)

currentEnv :: Expand VEnv
currentEnv = do
  phase <- currentPhase
  globalEnv <-  maybe Env.empty id . view (expanderWorld . worldEnvironments . at phase) <$> getState
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

visibleBindings :: Expand BindingTable
visibleBindings = do
  globals <- view expanderGlobalBindingTable <$> getState
  locals <- view expanderCurrentBindingTable <$> getState
  return (globals <> locals)


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


bind :: Binding -> EValue -> Expand ()
bind b v =
  modifyState $
  over expanderExpansionEnv $
  \(ExpansionEnv env) ->
    ExpansionEnv $ Map.insert b v env


allMatchingBindings :: Text -> ScopeSet -> Expand [(ScopeSet, Binding)]
allMatchingBindings x scs = do
  namesMatch <- view (at x . non []) <$> visibleBindings
  p <- currentPhase
  let scopesMatch =
        [ (scopes, b)
        | (scopes, b, _) <- namesMatch
        , ScopeSet.isSubsetOf p scopes scs
        ]
  return scopesMatch



checkUnambiguous :: ScopeSet -> [ScopeSet] -> Ident -> Expand ()
checkUnambiguous best candidates blame =
  do p <- currentPhase
     let bestSize = ScopeSet.size p best
     let candidateSizes = map (ScopeSet.size p) (nub candidates)
     if length (filter (== bestSize) candidateSizes) > 1
       then throwError (Ambiguous p blame candidates)
       else return ()

resolve :: Ident -> Expand Binding
resolve stx@(Stx scs srcLoc x) = do
  p <- currentPhase
  bs <- allMatchingBindings x scs
  case bs of
    [] ->
      throwError (Unknown (Stx scs srcLoc x))
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
  traverse_ (uncurry addTypePrimitive) typePrims

  where
    typePrims :: [(Text, SplitTypePtr -> Syntax -> Expand ())]
    typePrims =
      [ ( "Bool"
        , \ dest stx -> do
            _actualName <- mustBeIdent stx
            linkType dest TBool
        )
      , ( "Unit"
        , \ dest stx -> do
            _actualName <- mustBeIdent stx
            linkType dest TUnit
        )
      , ( "Syntax"
        , \ dest stx -> do
            _actualName <- mustBeIdent stx
            linkType dest TSyntax
        )
      , ( "Ident"
        , \ dest stx -> do
            _actualName <- mustBeIdent stx
            linkType dest TIdent
        )
      , ( "Signal"
        , \ dest stx -> do
            _actualName <- mustBeIdent stx
            linkType dest TSignal
        )
      , ( "->"
        , \ dest stx -> do
            Stx _ _ (_ :: Syntax, arg, ret) <- mustHaveEntries stx
            argDest <- scheduleType arg
            retDest <- scheduleType ret
            linkType dest (TFun argDest retDest)
        )
      , ( "Macro"
        , \ dest stx -> do
            Stx _ _ (_ :: Syntax, t) <- mustHaveEntries stx
            tDest <- scheduleType t
            linkType dest (TMacro tDest)
        )
      , ( "List"
        , \ dest stx -> do
            Stx _ _ (_ :: Syntax, e) <- mustHaveEntries stx
            entryTypeDest <- scheduleType e
            linkType dest (TList entryTypeDest)
        )
      ]

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
                Stx _ _ (_ :: Syntax, name, imports, body, exports) <- mustHaveEntries stx
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
            Stx _ _ (_, varStx, expr) <- mustHaveEntries stx
            x <- flip addScope' sc <$> mustBeIdent varStx
            b <- freshBinding
            addDefinedBinding x b
            var <- freshVar
            exprDest <- liftIO $ newSplitCorePtr
            bind b (EIncompleteDefn var x exprDest)
            schPtr <- liftIO $ newSchemePtr
            linkDecl dest (Define x var schPtr exprDest)
            forkExpandSyntax (ExprDest exprDest) expr
            forkCheckDecl dest
            nowValidAt pdest (SpecificPhase p)
        )
      ,("define-macros"
        , \ sc dest pdest stx -> do
            Stx _ _ (_ :: Syntax, macroList) <- mustHaveEntries stx
            Stx _ _ macroDefs <- mustBeList macroList
            p <- currentPhase
            macros <- for macroDefs $ \def -> do
              Stx _ _ (mname, mdef) <- mustHaveEntries def
              theName <- flip addScope' sc <$> mustBeIdent mname
              b <- freshBinding
              addDefinedBinding theName b
              macroDest <- inEarlierPhase $ schedule (addScope p mdef sc)
              v <- freshMacroVar
              bind b $ EIncompleteMacro v theName macroDest
              return (theName, v, macroDest)
            linkDecl dest $ DefineMacros macros
            nowValidAt pdest (SpecificPhase p)
        )
      , ("example"
        , \ sc dest pdest stx -> do
            p <- currentPhase
            Stx _ _ (_ :: Syntax, expr) <- mustHaveEntries stx
            exprDest <- liftIO $ newSplitCorePtr
            linkDecl dest (Example exprDest)
            forkExpandSyntax (ExprDest exprDest) (addScope p expr sc)
            nowValidAt pdest (SpecificPhase p)
        )
      , ("import"
         -- TODO Make import spec language extensible and use bindings rather than literals
        , \sc dest pdest stx -> do
            Stx scs loc (_ :: Syntax, toImport) <- mustHaveEntries stx
            spec <- importSpec toImport
            modExports <- getImports spec
            flip forExports_ modExports $ \p x b -> inPhase p do
              imported <- addRootScope' $ addScope' (Stx scs loc x) sc
              addImportBinding imported b
            linkDecl dest (Import spec)
            nowValidAt pdest AllPhases
        )
      , ("export"
        , \_sc dest pdest stx -> do
            Stx _ _ (_, protoSpec) <- mustBeCons stx
            exported <- exportSpec stx protoSpec
            p <- currentPhase
            es <- getExports exported
            modifyState $ over expanderModuleExports $ (<> es)
            linkDecl dest (Export exported)
            nowValidAt pdest (SpecificPhase p)
        )
      , ("meta"
        , \sc dest pdest stx -> do
            Stx _ _ (_ :: Syntax, subDecl) <- mustHaveEntries stx
            subDest <- liftIO newDeclPtr
            linkDecl dest (Meta subDest)
            inEarlierPhase $
              forkExpandOneDecl subDest sc pdest =<< addRootScope subDecl
        )
      ]
      where
        nowValidAt :: DeclValidityPtr -> PhaseSpec -> Expand ()
        nowValidAt ptr p =
          modifyState $ over expanderDeclPhases $ Map.insert ptr p

        importSpec :: Syntax -> Expand ImportSpec
        importSpec (Syntax (Stx scs srcloc (String s))) =
          ImportModule . Stx scs srcloc <$> liftIO (moduleNameFromLocatedPath srcloc (T.unpack s))
        importSpec (Syntax (Stx scs srcloc (Id "kernel"))) =
          return $ ImportModule (Stx scs srcloc (KernelName kernelName))
        importSpec stx@(Syntax (Stx _ _ (List elts)))
          | (Syntax (Stx _ _ (Id "only")) : spec : names) <- elts = do
              subSpec <- importSpec spec
              ImportOnly subSpec <$> traverse mustBeIdent names
          | (Syntax (Stx _ _ (Id "rename")) : spec : renamings) <- elts = do
              subSpec <- importSpec spec
              RenameImports subSpec <$> traverse getRename renamings
          | [Syntax (Stx _ _ (Id "shift")), spec, Syntax (Stx _ _ (Sig (Signal i)))] <- elts = do
              subSpec <- importSpec spec
              return $ ShiftImports subSpec (fromIntegral i)
          | [Syntax (Stx _ _ (Id "prefix")), spec, prefix] <- elts = do
            subSpec <- importSpec spec
            Stx _ _ p <- mustBeIdent prefix
            return $ PrefixImports subSpec p
          | otherwise = throwError $ NotImportSpec stx
          where
            getRename s = do
              Stx _ _ (old', new') <- mustHaveEntries s
              old <- mustBeIdent old'
              new <- mustBeIdent new'
              return (old, new)
        importSpec other = throwError $ NotImportSpec other

        exportSpec :: Syntax -> [Syntax] -> Expand ExportSpec
        exportSpec blame elts
          | [Syntax (Stx scs' srcloc'  (List ((getIdent -> Just (Stx _ _ kw)) : args)))] <- elts =
              case kw of
                "rename" ->
                  case args of
                    (rens : more) -> do
                      pairs <- getRenames rens
                      spec <- exportSpec blame more
                      return $ ExportRenamed spec pairs
                    _ -> throwError $ NotExportSpec blame
                "prefix" ->
                  case args of
                    ((syntaxE -> String pref) : more) -> do
                      spec <- exportSpec blame more
                      return $ ExportPrefixed spec pref
                    _ -> throwError $ NotExportSpec blame
                "shift" ->
                  case args of
                    (Syntax (Stx _ _ (Sig (Signal i))) : more) -> do
                      spec <- exportSpec (Syntax (Stx scs' srcloc' (List more))) more
                      if i >= 0
                        then return $ ExportShifted spec (fromIntegral i)
                        else throwError $ NotExportSpec blame
                    _ -> throwError $ NotExportSpec blame
                _ -> throwError $ NotExportSpec blame
          | Just xs <- traverse getIdent elts = return (ExportIdents xs)
          | otherwise = throwError $ NotExportSpec blame
          where
            getIdent (Syntax (Stx scs loc (Id x))) = pure (Stx scs loc x)
            getIdent _ = empty
            getRenames :: Syntax -> Expand [(Text, Text)]
            getRenames (syntaxE -> List rens) =
              for rens $ \stx -> do
                Stx _ _ (x, y) <- mustHaveEntries stx
                Stx _ _ x' <- mustBeIdent x
                Stx _ _ y' <- mustBeIdent y
                pure (x', y')
            getRenames _ = throwError $ NotExportSpec blame

    exprPrims :: [(Text, SplitCorePtr -> Syntax -> Expand ())]
    exprPrims =
      [ ( "oops"
        , \ _ stx -> throwError (InternalError $ "oops" ++ show stx)
        )
      , ( "the"
        , \ dest stx -> do
            Stx _ _ (_, ty, expr) <- mustHaveEntries stx
            tyDest <- scheduleType ty
            -- TODO add type to elaborated program? Or not?
            forkExpandSyntax (ExprDest dest) expr
            forkTypeCheck dest tyDest
        )
      , ( "let"
        , \ dest stx -> do
            Stx _ _ (_, b, body) <- mustHaveEntries stx
            Stx _ _ (x, def) <- mustHaveEntries b
            (sc, x', coreX) <- prepareVar x
            p <- currentPhase
            psc <- phaseRoot
            defDest <- schedule def
            bodyDest <- schedule $ addScope p (addScope p body sc) psc
            linkExpr dest $ CoreLet x' coreX defDest bodyDest
        )
      , ( "flet"
        , \ dest stx -> do
            Stx _ _ (_, b, body) <- mustHaveEntries stx
            Stx _ _ (f, args, def) <- mustHaveEntries b
            Stx _ _ x <- mustHaveEntries args
            (fsc, f', coreF) <- prepareVar f
            (xsc, x', coreX) <- prepareVar x
            p <- currentPhase
            psc <- phaseRoot
            defDest <- schedule $
                       addScope p (addScope p (addScope p def fsc) xsc) psc
            bodyDest <- schedule $ addScope p (addScope p body fsc) psc
            linkExpr dest $ CoreLetFun f' coreF x' coreX defDest bodyDest
        )
      , ( "lambda"
        , \ dest stx -> do
            Stx _ _ (_, arg, body) <- mustHaveEntries stx
            Stx _ _ theArg <- mustHaveEntries arg
            (sc, arg', coreArg) <- prepareVar theArg
            p <- currentPhase
            psc <- phaseRoot
            bodyDest <- schedule $ addScope p (addScope p body sc) psc
            linkExpr dest $ CoreLam arg' coreArg bodyDest
        )
      , ( "#%app"
        , \ dest stx -> do
            Stx _ _ (_, fun, arg) <- mustHaveEntries stx
            funDest <- schedule fun
            argDest <- schedule arg
            linkExpr dest $ CoreApp funDest argDest
        )
      , ( "pure"
        , \ dest stx -> do
            Stx _ _ (_ :: Syntax, v) <- mustHaveEntries stx
            argDest <- schedule v
            linkExpr dest $ CorePure argDest
        )
      , ( ">>="
        , \ dest stx -> do
            Stx _ _ (_, act, cont) <- mustHaveEntries stx
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
            Stx _ _ (_ :: Syntax, sig) <- mustHaveEntries stx
            sigDest <- schedule sig
            linkExpr dest $ CoreSendSignal sigDest
        )
      , ( "wait-signal"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, sig) <- mustHaveEntries stx
            sigDest <- schedule sig
            linkExpr dest $ CoreWaitSignal sigDest
        )
      , ( "bound-identifier=?"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, id1, id2) <- mustHaveEntries stx
            newE <- CoreIdentEq Bound <$> schedule id1 <*> schedule id2
            linkExpr dest newE
        )
      , ( "free-identifier=?"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, id1, id2) <- mustHaveEntries stx
            newE <- CoreIdentEq Free <$> schedule id1 <*> schedule id2
            linkExpr dest newE
        )
      , ( "quote"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, quoted) <- mustHaveEntries stx
            linkExpr dest $ CoreSyntax quoted
        )
      , ( "if"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, b, t, f) <- mustHaveEntries stx
            linkExpr dest =<< CoreIf <$> schedule b <*> schedule t <*> schedule f
        )
      , ( "ident"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, someId) <- mustHaveEntries stx
            x@(Stx _ _ _) <- mustBeIdent someId
            linkExpr dest $ CoreIdentifier x
        )
      , ( "ident-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, someId, source) <- mustHaveEntries stx
            idDest <- schedule someId
            sourceDest <- schedule source
            linkExpr dest $ CoreIdent $ ScopedIdent idDest sourceDest
        )
      , ( "empty-list-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, source) <- mustHaveEntries stx
            sourceDest <- schedule source
            linkExpr dest $ CoreEmpty $ ScopedEmpty sourceDest
        )
      , ( "cons-list-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, car, cdr, source) <- mustHaveEntries stx
            carDest <- schedule car
            cdrDest <- schedule cdr
            sourceDest <- schedule source
            linkExpr dest $ CoreCons $ ScopedCons carDest cdrDest sourceDest
        )
      , ( "list-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, list, source) <- mustHaveEntries stx
            Stx _ _ listItems <- mustHaveEntries list
            listDests <- traverse schedule listItems
            sourceDest <- schedule source
            linkExpr dest $ CoreList $ ScopedList listDests sourceDest
        )
      , ( "syntax-case"
        , \dest stx -> do
            Stx scs loc (_ :: Syntax, args) <- mustBeCons stx
            Stx _ _ (scrutinee, patterns) <- mustBeCons (Syntax (Stx scs loc (List args)))
            scrutDest <- schedule scrutinee
            patternDests <- traverse (mustHaveEntries >=> expandPatternCase) patterns
            linkExpr dest $ CoreCase scrutDest patternDests
        )
      , ( "let-syntax"
        , \dest stx -> do
            Stx _ loc (_ :: Syntax, macro, body) <- mustHaveEntries stx
            Stx _ _ (mName, mdef) <- mustHaveEntries macro
            sc <- freshScope $ T.pack $ "Scope for let-syntax at " ++ shortShow loc
            m <- mustBeIdent mName
            p <- currentPhase
            -- Here, the binding occurrence of the macro gets the
            -- fresh scope at all phases, but later, the scope is only
            -- added to the correct phase in potential use sites.
            -- This prevents the body of the macro (in an earlier
            -- phase) from being able to refer to the macro itself.
            let m' = addScope' m sc
            b <- freshBinding
            addLocalBinding m' b
            v <- freshMacroVar
            macroDest <- inEarlierPhase $ do
              psc <- phaseRoot
              schedule (addScope (prior p) mdef psc)
            forkAwaitingMacro b v m' macroDest dest (addScope p body sc)
        )
      , ( "log"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, message) <- mustHaveEntries stx
            msgDest <- schedule message
            linkExpr dest $ CoreLog msgDest
        )
      ]

    expandPatternCase :: Stx (Syntax, Syntax) -> Expand (Pattern, SplitCorePtr)
    -- TODO match case keywords hygienically
    expandPatternCase (Stx _ _ (lhs, rhs)) = do
      p <- currentPhase
      case lhs of
        Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "ident")),
                               patVar])) -> do
          (sc, x', var) <- prepareVar patVar
          let rhs' = addScope p rhs sc
          rhsDest <- schedule rhs'
          let patOut = PatternIdentifier x' var
          return (patOut, rhsDest)
        Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "list")),
                               Syntax (Stx _ _ (List vars))])) -> do
          varInfo <- traverse prepareVar vars
          let rhs' = foldr (flip (addScope p)) rhs [sc | (sc, _, _) <- varInfo]
          rhsDest <- schedule rhs'
          let patOut = PatternList [(ident, var) | (_, ident, var) <- varInfo]
          return (patOut, rhsDest)
        Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "cons")),
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
        Syntax (Stx _ _ (Id "_")) -> do
          rhsDest <- schedule rhs
          return (PatternAny, rhsDest)
        other ->
          throwError $ UnknownPattern other

    prepareVar :: Syntax -> Expand (Scope, Ident, Var)
    prepareVar varStx = do
      sc <- freshScope $ T.pack $ "For variable " ++ shortShow varStx
      x <- mustBeIdent varStx
      p <- currentPhase
      psc <- phaseRoot
      let x' = addScope' (addScope p x sc) psc
      b <- freshBinding
      addLocalBinding x' b
      var <- freshVar
      bind b (EVarMacro var)
      return (sc, x', var)

    scheduleType :: Syntax -> Expand SplitTypePtr
    scheduleType stx = do
      dest <- liftIO newSplitTypePtr
      forkExpandType dest stx
      return dest

    schedule :: Syntax -> Expand SplitCorePtr
    schedule stx = do
      dest <- liftIO newSplitCorePtr
      forkExpandSyntax (ExprDest dest) stx
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

    addTypePrimitive :: Text -> (SplitTypePtr -> Syntax -> Expand ()) -> Expand ()
    addTypePrimitive name impl = do
      let val = EPrimTypeMacro impl
      b <- freshBinding
      bind b val
      addToKernel name runtime b

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
  modifyState $ over expanderCompletedModBody (<> Map.singleton dest Done)
forkExpandDecls dest (Syntax (Stx scs loc (List (d:ds)))) = do
  -- Create a scope for this new declaration
  sc <- freshScope $ T.pack $ "For declaration at " ++ shortShow (stxLoc d)
  restDest <- liftIO $ newModBodyPtr
  declDest <- liftIO $ newDeclPtr
  declPhase <- newDeclValidityPtr
  modifyState $ over expanderCompletedModBody $
    (<> Map.singleton dest (Decl declDest restDest))
  forkExpanderTask $
    ExpandMoreDecls restDest sc
      (Syntax (Stx scs loc (List ds)))
      declPhase
  forkExpandOneDecl declDest sc declPhase =<< addRootScope d
  where
    stxLoc (Syntax (Stx _ srcloc _)) = srcloc
forkExpandDecls _dest _other =
  error "TODO real error message - malformed module body"


identifierHeaded :: Syntax -> Maybe Ident
identifierHeaded (Syntax (Stx scs srcloc (Id x))) = Just (Stx scs srcloc x)
identifierHeaded (Syntax (Stx _ _ (List (h:_))))
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
runTask (tid, localData, task) = withLocal localData $ do
  case task of
    ExpandSyntax dest stx ->
      case dest of
        ExprDest d ->
          expandOneExpression d stx
        DeclDest d sc ph ->
          expandOneDeclaration sc d stx ph
        TypeDest d -> expandOneType d stx
    AwaitingSignal dest signal kont -> do
      signalWasSent <- viewIORef expanderState (expanderReceivedSignals . at signal)
      case signalWasSent of
        Nothing -> do
          stillStuck tid task
        Just () -> do
          let result = ValueSignal signal  -- TODO: return unit instead
          forkContinueMacroAction dest result kont
    AwaitingMacro dest (TaskAwaitMacro b v x deps mdest stx) -> do
      newDeps <- concat <$> traverse dependencies deps
      case newDeps of
        (_:_) -> do
          tid' <- if Set.fromList newDeps == Set.fromList deps
                    then return tid
                    else newTaskID
          laterMacro tid' b v x dest newDeps mdest stx
        [] ->
          linkedCore mdest >>=
          \case
            Nothing -> error "Internal error - macro body not fully expanded"
            Just macroImpl -> do
              p <- currentPhase
              macroImplVal <- inEarlierPhase $ expandEval $ eval macroImpl
              let tenv = Env.singleton v x macroImplVal
              -- Extend the env!
              modifyState $ over (expanderCurrentTransformerEnvs . at p) $
                Just . maybe tenv (<> tenv)
              bind b $ EUserMacro v
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
              forkExpandSyntax (ExprDest dest) stx
        Just _v -> do
          bind b $ EVarMacro x
          forkExpandSyntax (ExprDest dest) stx
    ExpandDecl dest sc stx ph ->
      expandOneDeclaration sc dest stx ph
    ExpandMoreDecls dest sc stx waitingOn -> do
      readyYet <- view (expanderDeclPhases . at waitingOn) <$> getState
      case readyYet of
        Nothing ->
          stillStuck tid task
        Just (SpecificPhase p) ->
          forkExpandDecls dest (addScope p stx sc)
        Just AllPhases ->
          forkExpandDecls dest (addScope' stx sc)
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
    TypeCheck eDest ty -> do
      st <- getState
      let eTop = view (expanderCompletedCore . at eDest) st
      case eTop of
        Nothing -> stillStuck tid task
        Just e ->
          case ty of
            IncompleteType tDest ->
              linkedType tDest >>=
              \case
                Nothing -> stillStuck tid task
                Just t ->
                  typeCheckLayer eDest e t
            CompleteType t ->
              typeCheckLayer eDest e t
    TypeCheckDecl dest -> do
      st <- getState
      case view (expanderCompletedDecls . at dest) st of
        Nothing -> stillStuck tid task
        Just d -> typeCheckDecl d
    GeneralizeType edest ty schdest -> do
      ready <- isExprChecked edest
      if ready
        then do
          st <- getState
          case view (expanderExpressionTypes . at edest) st of
            Nothing -> throwError $ InternalError "Type not found during generalization"
            Just _ -> do
              sch <- generalizeType ty
              linkScheme schdest sch
        else stillStuck tid task
    TypeCheckVar eDest ty ->
      linkedCore eDest >>=
      \case
        Nothing -> stillStuck tid task
        Just (Core (CoreVar x)) ->
          varType x >>=
          \case
            Nothing -> stillStuck tid task
            Just sch -> do
              specialize sch >>= unify ty
              saveExprType eDest ty
        Just _ ->
          throwError $ InternalError "Not a variable when specializing"

  where
    laterMacro tid' b v x dest deps mdest stx = do
      localConfig <- view expanderLocal
      modifyState $
        over expanderTasks $
          ((tid', localConfig, AwaitingMacro dest (TaskAwaitMacro b v x deps mdest stx)) :)

expandOneType :: SplitTypePtr -> Syntax -> Expand ()
expandOneType dest stx
  | Just ident <- identifierHeaded stx = do
      b <- resolve =<< addRootScope ident
      v <- getEValue b
      case v of
        EPrimTypeMacro impl -> impl dest stx
        EPrimMacro _ -> throwError $ InternalError "Context expects a type"
        EPrimDeclMacro _ -> throwError $ InternalError "Context expects a type"
        EVarMacro _ -> throwError $ InternalError "Context expects a type, but got a program variable"
        EPrimModuleMacro _ -> throwError $ InternalError "Context expects a type, not a module"
        EIncompleteMacro _ _ _ ->
          throwError $ InternalError "Context expects a type"
        EIncompleteDefn _ _ _ ->
          throwError $ InternalError "Context expects a type"
        EUserMacro transformerName -> do
          stepScope <- freshScope $ T.pack $ "Expansion step for " ++ shortShow ident
          p <- currentPhase
          implV <- Env.lookupVal transformerName <$> currentTransformerEnv
          case implV of
            Just (ValueClosure macroImpl) -> do
              macroVal <- inEarlierPhase $ expandEval $
                          apply macroImpl $
                          ValueSyntax $ addScope p stx stepScope
              case macroVal of
                ValueMacroAction act -> do
                  res <- interpretMacroAction act
                  case res of
                    Left (sig, kont) -> do
                      forkAwaitingSignal (TypeDest dest) sig kont
                    Right expanded ->
                      case expanded of
                        ValueSyntax expansionResult ->
                          forkExpandSyntax (TypeDest dest) (flipScope p expansionResult stepScope)
                        other -> throwError $ ValueNotSyntax other
                other ->
                  throwError $ ValueNotMacro other
            Nothing ->
              throwError $ InternalError $
              "No transformer yet created for " ++ shortShow ident ++
              " (" ++ show transformerName ++ ") at phase " ++ shortShow p
            Just other -> throwError $ ValueNotMacro other
  | otherwise = throwError $ NotValidType stx


expandOneExpression :: SplitCorePtr -> Syntax -> Expand ()
expandOneExpression dest stx
  | Just ident <- identifierHeaded stx = do
      b <- resolve =<< addRootScope ident
      v <- getEValue b
      case v of
        EPrimMacro impl -> impl dest stx
        EPrimTypeMacro _ -> throwError $ InternalError "Current context won't accept types"
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
        EIncompleteMacro transformerName sourceIdent mdest -> do
          forkAwaitingMacro b transformerName sourceIdent mdest dest stx
        EIncompleteDefn x n d ->
          forkAwaitingDefn x n b d dest stx
        EUserMacro transformerName -> do
          stepScope <- freshScope $ T.pack $ "Expansion step for " ++ shortShow ident
          p <- currentPhase
          implV <- Env.lookupVal transformerName <$> currentTransformerEnv
          case implV of
            Just (ValueClosure macroImpl) -> do
              macroVal <- inEarlierPhase $ expandEval $
                          apply macroImpl $
                          ValueSyntax $ addScope p stx stepScope
              case macroVal of
                ValueMacroAction act -> do
                  res <- interpretMacroAction act
                  case res of
                    Left (sig, kont) -> do
                      forkAwaitingSignal (ExprDest dest) sig kont
                    Right expanded ->
                      case expanded of
                        ValueSyntax expansionResult ->
                          forkExpandSyntax (ExprDest dest) (flipScope p expansionResult stepScope)
                        other -> throwError $ ValueNotSyntax other
                other ->
                  throwError $ ValueNotMacro other
            Nothing ->
              throwError $ InternalError $
              "No transformer yet created for " ++ shortShow ident ++
              " (" ++ show transformerName ++ ") at phase " ++ shortShow p
            Just other -> throwError $ ValueNotMacro other
  | otherwise =
    case syntaxE stx of
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
      b <- resolve =<< addRootScope ident
      v <- getEValue b
      case v of
        EPrimMacro _ ->
          throwError $ InternalError "Current context won't accept expressions"
        EPrimModuleMacro _ ->
          throwError $ InternalError "Current context won't accept modules"
        EPrimDeclMacro impl ->
          impl sc dest ph stx
        EPrimTypeMacro _ ->
          throwError $ InternalError "Current context won't accept types"
        EVarMacro _ ->
          throwError $ InternalError "Current context won't accept expressions"
        EIncompleteDefn _ _ _ ->
          throwError $ InternalError "Current context won't accept expressions"
        EUserMacro transformerName -> do
          stepScope <- freshScope $ T.pack $ "Expansion step for decl " ++ shortShow ident
          p <- currentPhase
          implV <- Env.lookupVal transformerName <$> currentTransformerEnv
          case implV of
            Just (ValueClosure macroImpl) -> do
              macroVal <- inEarlierPhase $ expandEval $
                          apply macroImpl $
                          ValueSyntax $ addScope p stx stepScope
              case macroVal of
                ValueMacroAction act -> do
                  res <- interpretMacroAction act
                  case res of
                    Left (sig, kont) -> do
                      forkAwaitingSignal (DeclDest dest sc ph) sig kont
                    Right expanded ->
                      case expanded of
                        ValueSyntax expansionResult ->
                          forkExpandSyntax (DeclDest dest sc ph) (flipScope p expansionResult stepScope)
                        other -> throwError $ ValueNotSyntax other
                other ->
                  throwError $ ValueNotMacro other
            Nothing ->
              throwError $ InternalError $
              "No transformer yet created for " ++ shortShow ident ++
              " (" ++ show transformerName ++ ") at phase " ++ shortShow p
            Just other -> throwError $ ValueNotMacro other

        EIncompleteMacro transformerName sourceIdent mdest ->
          forkAwaitingDeclMacro b transformerName sourceIdent mdest dest sc ph stx
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
    Free ->
      compareFree id1 id2
        `catchError`
        \case
          -- Ambiguous bindings should not crash the comparison -
          -- they're just not free-identifier=?.
          Ambiguous _ _ _ -> return $ Right $ ValueBool $ False
          -- Similarly, things that are not yet bound are just not
          -- free-identifier=?
          Unknown _ -> return $ Right $ ValueBool $ False
          e -> throwError e
    Bound ->
      return $ Right $ ValueBool $ view stxScopeSet id1 == view stxScopeSet id2
  where
    getIdent (ValueSyntax stx) = mustBeIdent stx
    getIdent _other = throwError $ InternalError $ "Not a syntax object in " ++ opName
    compareFree id1 id2 = do
      b1 <- resolve id1
      b2 <- resolve id2
      return $ Right $ ValueBool $ b1 == b2
    opName =
      case how of
        Free  -> "free-identifier=?"
        Bound -> "bound-identifier=?"
interpretMacroAction (MacroActionLog stx) = do
  liftIO $ prettyPrint stx >> putStrLn ""
  pure $ Right (ValueBool False) -- TODO unit type

-- | Invariant: the SplitCorePtr points at the CoreF in question
typeCheckLayer :: SplitCorePtr -> CoreF SplitCorePtr -> Ty -> Expand ()
typeCheckLayer dest (CoreVar _) t =
  forkCheckVar dest t
typeCheckLayer dest (CoreLet x ident def body) t = do
  xTy <- inTypeBinder do
    xt <- Ty . TMetaVar <$> freshMeta
    forkCompleteTypeCheck def xt
    return xt
  sch <- liftIO $ newSchemePtr
  forkGeneralizeType def xTy sch
  withLocalVarType x ident sch $
    forkCompleteTypeCheck body t
  saveExprType dest t
typeCheckLayer dest (CoreLetFun f fident x xident def body) t = do
  ft <- inTypeBinder $ Ty . TMetaVar <$> freshMeta
  xt <- inTypeBinder $ Ty . TMetaVar <$> freshMeta
  rt <- inTypeBinder $ Ty . TMetaVar <$> freshMeta
  fsch <- trivialScheme ft
  xsch <- trivialScheme xt
  inTypeBinder $
    withLocalVarType f fident fsch $
      withLocalVarType x xident xsch $
        forkCompleteTypeCheck def rt
  unify ft (Ty (TFun xt rt))
  sch <- liftIO newSchemePtr
  forkGeneralizeType def ft sch
  withLocalVarType f fident sch $
    forkCompleteTypeCheck body t
  saveExprType dest t
typeCheckLayer dest (CoreLam x ident body) t = do
  argT <- Ty . TMetaVar <$> freshMeta
  retT <- Ty . TMetaVar <$> freshMeta
  unify t (Ty (TFun argT retT))
  sch <- trivialScheme argT
  withLocalVarType x ident sch $
    forkCompleteTypeCheck body retT
  saveExprType dest t
typeCheckLayer dest (CoreApp fun arg) t = do
  argT <- Ty . TMetaVar <$> freshMeta
  forkCompleteTypeCheck fun (Ty (TFun argT t))
  forkCompleteTypeCheck arg argT
  saveExprType dest t
typeCheckLayer dest (CorePure e) t = do
  innerT <- Ty . TMetaVar <$> freshMeta
  unify (Ty (TMacro innerT)) t
  forkCompleteTypeCheck e innerT
  saveExprType dest t
typeCheckLayer dest (CoreBind e1 e2) t = do
  a <- Ty . TMetaVar <$> freshMeta
  forkCompleteTypeCheck e1 (Ty (TMacro a))
  b <- Ty . TMetaVar <$> freshMeta
  forkCompleteTypeCheck e2 (Ty (TFun a (Ty (TMacro b))))
  unify t (Ty (TMacro b))
  saveExprType dest t
typeCheckLayer dest (CoreSyntaxError (SyntaxError locs msg)) t = do
  for_ locs (flip forkCompleteTypeCheck (Ty TSyntax))
  forkCompleteTypeCheck msg (Ty TSyntax)
  a <- Ty . TMetaVar <$> freshMeta
  unify t (Ty (TMacro a))
  saveExprType dest t
typeCheckLayer dest (CoreSendSignal s) t = do
  forkCompleteTypeCheck s (Ty TSignal)
  unify t (Ty (TMacro (Ty TUnit)))
  saveExprType dest t
typeCheckLayer dest (CoreWaitSignal s) t = do
  forkCompleteTypeCheck s (Ty TSignal)
  unify t (Ty (TMacro (Ty TUnit)))
  saveExprType dest t
typeCheckLayer dest (CoreIdentEq _ e1 e2) t = do
  forkCompleteTypeCheck e1 (Ty TSyntax)
  forkCompleteTypeCheck e2 (Ty TSyntax)
  unify t (Ty (TMacro (Ty TBool)))
  saveExprType dest t
typeCheckLayer dest (CoreLog msg) t = do
  forkCompleteTypeCheck msg (Ty TSyntax)
  unify t (Ty (TMacro (Ty TUnit)))
  saveExprType dest t
typeCheckLayer dest (CoreSyntax _) t = do
  unify (Ty TSyntax) t
  saveExprType dest t
typeCheckLayer dest (CoreCase scrutinee cases) t = do
  forkCompleteTypeCheck scrutinee (Ty TSyntax)
  for_ cases $ \ (pat, expr) ->
    bindVars pat $ forkCompleteTypeCheck expr t
  saveExprType dest t
  where
    bindVars (PatternIdentifier ident x) act = do
      sch <- trivialScheme (Ty TIdent)
      withLocalVarType ident x sch act
    bindVars PatternEmpty act = act
    bindVars (PatternCons identA a identD d) act = do
      stxT <- trivialScheme (Ty TSyntax)
      lstT <- trivialScheme (Ty (TList (Ty TSyntax)))
      withLocalVarType identA a stxT $
        withLocalVarType identD d lstT $
          act
    bindVars (PatternList []) act = act
    bindVars (PatternList ((ident, x) : more)) act = do
      sch <- trivialScheme (Ty TSyntax)
      withLocalVarType ident x sch $
        bindVars (PatternList more) act
    bindVars PatternAny act = act
typeCheckLayer dest (CoreIdentifier _ident) t = do
  unify t (Ty (TIdent))
  saveExprType dest t
typeCheckLayer dest (CoreSignal _s) t = do
  unify t (Ty (TSignal))
  saveExprType dest t
typeCheckLayer dest (CoreBool _) t = do
  unify (Ty TBool) t
  saveExprType dest t
typeCheckLayer dest (CoreIf b e1 e2) t = do
  forkCompleteTypeCheck b (Ty TBool)
  forkCompleteTypeCheck e1 t
  forkCompleteTypeCheck e2 t
  saveExprType dest t
typeCheckLayer dest (CoreIdent (ScopedIdent ident srcloc)) t = do
  forkCompleteTypeCheck ident (Ty TIdent)
  forkCompleteTypeCheck srcloc (Ty TSyntax)
  unify t (Ty TIdent)
  saveExprType dest t
typeCheckLayer dest (CoreEmpty (ScopedEmpty srcloc)) t = do
  unify t (Ty TSyntax)
  forkCompleteTypeCheck srcloc (Ty TSyntax)
  saveExprType dest t
typeCheckLayer dest (CoreCons (ScopedCons hd tl srcloc)) t = do
  forkCompleteTypeCheck hd (Ty TSyntax)
  forkCompleteTypeCheck tl (Ty (TList (Ty TSyntax)))
  forkCompleteTypeCheck srcloc (Ty TSyntax)
  unify t (Ty TSyntax)
  saveExprType dest t
typeCheckLayer dest (CoreList (ScopedList elts srcloc)) t = do
  for_ elts $ \e -> forkCompleteTypeCheck e t
  forkCompleteTypeCheck srcloc (Ty TSyntax)
  unify t (Ty TSyntax)
  saveExprType dest t

typeCheckDecl :: Decl SchemePtr DeclPtr SplitCorePtr -> Expand ()
typeCheckDecl (Define x v sch e) = do
  ty <- inTypeBinder do
    tdest <- liftIO newSplitTypePtr
    meta <- freshMeta
    linkType tdest (TMetaVar meta)
    forkTypeCheck e tdest
    return (TMetaVar meta)
  ph <- currentPhase
  modifyState $ over (expanderDefTypes . at ph . non Env.empty) $
    Env.insert v x sch
  forkGeneralizeType e (Ty ty) sch

typeCheckDecl (DefineMacros macros) = error "TODO"
typeCheckDecl (Meta d) = inEarlierPhase $ forkCheckDecl d
typeCheckDecl (Example e) = error "TODO"
typeCheckDecl (Import _) = pure ()
typeCheckDecl (Export _) = pure ()


-- The expected type is first, the received is second
unify :: Ty -> Ty -> Expand ()
unify t1 t2 = do
  t1' <- normType t1
  t2' <- normType t2
  unify' (unTy t1') (unTy t2')

  where
    -- Rigid-rigid
    unify' TBool TBool = pure ()
    unify' TUnit TUnit = pure ()
    unify' TSyntax TSyntax = pure ()
    unify' TIdent TIdent = pure ()
    unify' TSignal TSignal = pure ()
    unify' (TFun a c) (TFun b d) = unify b a >> unify c d
    unify' (TMacro a) (TMacro b) = unify a b
    unify' (TList a) (TList b) = unify a b

    -- Flex-flex
    unify' (TMetaVar ptr1) (TMetaVar ptr2) = do
      l1 <- view varLevel <$> derefType ptr1
      l2 <- view varLevel <$> derefType ptr2
      if | ptr1 == ptr2 -> pure ()
         | l1 < l2 -> linkToType ptr1 t2
         | otherwise -> linkToType ptr2 t1

    -- Flex-rigid
    unify' (TMetaVar ptr1) _ = linkToType ptr1 t2
    unify' _ (TMetaVar ptr2) = linkToType ptr2 t1

    -- Mismatch
    unify' expected received = throwError $ TypeMismatch (show expected) (show received) -- TODO structured repr
