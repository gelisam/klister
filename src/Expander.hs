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
import Numeric.Natural
import System.Directory

import Binding
import Binding.Info
import Control.Lens.IORef
import Core
import Datatype
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
  t <- Ty . TMetaVar <$> freshMeta
  forkExpandSyntax (ExprDest t dest) stx
  expandTasks
  children <- view expanderCompletedCore <$> getState
  patterns <- view expanderCompletedPatterns <$> getState
  return $ SplitCore { _splitCoreRoot = dest
                     , _splitCoreDescendants = children
                     , _splitCorePatterns = patterns
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
  startDefTypes <- view expanderDefTypes <$> getState
  local (set (expanderLocal . expanderModuleName) thisMod) do
    lang <- mustBeModName (view moduleLanguage src)
    initializeLanguage lang
    declTreeDest <- liftIO $ newDeclTreePtr
    vp <- newDeclValidityPtr
    modifyState $ set expanderModuleTop $ Just declTreeDest
    decls <- addModuleScope (view moduleContents src)
    expandDeclForms declTreeDest mempty vp decls
    expandTasks
    body <- getDeclGroup declTreeDest
    let modName = view moduleSource src
    let theModule = Module { _moduleName = modName
                           , _moduleImports = noImports
                           , _moduleBody = body
                           , _moduleExports = noExports
                           }
    bs <- view expanderCurrentBindingTable <$> getState
    modifyState $ set expanderCurrentBindingTable startBindings
    modifyState $ set expanderDefTypes startDefTypes
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
evalMod (Expanded em _) = execWriterT $ do
    traverseOf_ (moduleBody . each) evalDecl em
  where
    evalDecl :: CompleteDecl -> WriterT [EvalResult] Expand ()
    evalDecl (CompleteDecl d) =
      case d of
        Define x n sch e -> do
          ptr <- liftIO newSchemePtr
          lift $ linkScheme ptr sch
          val <- lift $ expandEval (eval e)
          p <- lift currentPhase
          lift $ modifyState $
            over (expanderWorld . worldTypeContexts . at p . non Env.empty) $
            Env.insert n x ptr
          lift $ modifyState $
            over (expanderWorld . worldEnvironments . at p . non Env.empty) $
              Env.insert n x val
        Data _ dn arity ctors -> do
          p <- lift currentPhase
          let mn = view moduleName em
          let dt = Datatype { _datatypeModule = mn
                            , _datatypeName = dn
                            }
          for_ ctors \(_, cn, argTypes) ->
            lift $ modifyState $
            over (expanderWorld . worldConstructors . at p . non Map.empty) $
            Map.insert cn (ConstructorInfo argTypes dt)
          lift $ modifyState $
            over (expanderWorld . worldDatatypes . at p . non Map.empty) $
            Map.insert dt (DatatypeInfo arity [c | (_, c, _) <- ctors ])

        Example loc sch expr -> do
          env <- lift currentEnv
          value <- lift $ expandEval (eval expr)
          tell $ [EvalResult { resultLoc = loc
                             , resultEnv = env
                             , resultExpr = expr
                             , resultType = sch
                             , resultValue = value
                             }]

        DefineMacros macros -> do
          p <- lift currentPhase
          lift $ inEarlierPhase $ for_ macros $ \(x, n, e) -> do
            v <- expandEval (eval e)
            modifyState $
              over (expanderWorld . worldTransformerEnvironments . at p . non Env.empty) $
                Env.insert n x v
        Meta decls -> do
          ((), out) <- lift $ inEarlierPhase (runWriterT $ traverse_ evalDecl decls)
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
      let baseType =
            \name ctor ->
              (name, \ dest stx -> do
                       _actualName <- mustBeIdent stx
                       linkType dest ctor)
      in [ baseType "Bool" TBool
         , baseType "Unit" TUnit
         , baseType "Syntax" TSyntax
         , baseType "Signal" TSignal
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
                bodyPtr <- liftIO newDeclTreePtr
                modifyState $ set expanderModuleTop (Just bodyPtr)
                Stx _ _ (_ :: Syntax, name, imports, body, exports) <- mustHaveEntries stx
                _actualName <- mustBeIdent name

                resolveImports imports

                vp <- newDeclValidityPtr
                expandDeclForms bodyPtr mempty vp body

                buildExports exports
                pure ()
        )
      ]

    declPrims :: [(Text, DeclTreePtr -> ScopeSet -> DeclValidityPtr -> Syntax -> Expand ())]
    declPrims =
      [ ( "define"
        , \ dest scs vp stx -> do
            p <- currentPhase
            Stx _ _ (_, varStx, expr) <- mustHaveEntries stx
            sc <- freshScope $ T.pack $ "For definition at " ++ shortShow (stxLoc stx)
            x <- flip addScope' sc <$> mustBeIdent varStx
            b <- freshBinding
            addDefinedBinding x b
            var <- freshVar
            exprDest <- liftIO $ newSplitCorePtr
            bind b (EIncompleteDefn var x exprDest)
            schPtr <- liftIO $ newSchemePtr
            linkOneDecl dest (Define x var schPtr exprDest)
            t <- inTypeBinder do
              t <- Ty . TMetaVar <$> freshMeta
              forkExpandSyntax (ExprDest t exprDest) expr
              return t
            ph <- currentPhase
            modifyState $ over (expanderDefTypes . at ph . non Env.empty) $
              Env.insert var x schPtr
            forkGeneralizeType exprDest t schPtr
            linkDeclValidity vp (ScopeSet.insertAtPhase p sc scs)
        )
      , ( "datatype"
        , \ dest scs vp stx -> do
            Stx stxScs loc (_ :: Syntax, more) <- mustBeCons stx
            Stx _ _ (nameAndArgs, ctorSpecs) <- mustBeCons (Syntax (Stx stxScs loc (List more)))
            Stx _ _ (name, args) <- mustBeCons nameAndArgs
            typeArgs <- for (zip [0..] args) $ \(i, a) ->
              prepareTypeVar i a
            sc <- freshScope $ T.pack $ "For datatype at " ++ shortShow (stxLoc stx)
            let typeScopes = map fst typeArgs ++ [sc]
            realName <- mustBeIdent (addScope' name sc)
            p <- currentPhase
            let arity = length args
            d <- freshDatatype realName
            addDatatype realName d (fromIntegral arity)

            ctors <- for ctorSpecs \ spec -> do
              Stx _ _ (cn, ctorArgs) <- mustBeCons spec
              realCN <- mustBeIdent cn
              ctor <- freshConstructor realCN
              let ctorArgs' = [ foldr (flip (addScope p)) t typeScopes
                              | t <- ctorArgs
                              ]
              argTypes <- traverse scheduleType ctorArgs'
              return (realCN, ctor, argTypes)

            let info =
                  DatatypeInfo
                  { _datatypeArity = fromIntegral arity
                  , _datatypeConstructors =
                    [ ctor | (_, ctor, _) <- ctors ]
                  }
            modifyState $
              set (expanderCurrentDatatypes .
                   at p . non Map.empty .
                   at d) $
              Just info


            forkEstablishConstructors (ScopeSet.insertAtPhase p sc scs) vp d ctors

            linkOneDecl dest (Data realName (view datatypeName d) (fromIntegral arity) ctors)
        )
      , ( "define-macros"
        , \ dest scs vp stx -> do
            Stx _ _ (_ :: Syntax, macroList) <- mustHaveEntries stx
            Stx _ _ macroDefs <- mustBeList macroList
            p <- currentPhase
            sc <- freshScope $ T.pack $ "For macros at " ++ shortShow (stxLoc stx)
            macros <- for macroDefs $ \def -> do
              Stx _ _ (mname, mdef) <- mustHaveEntries def
              theName <- flip addScope' sc <$> mustBeIdent mname
              b <- freshBinding
              addDefinedBinding theName b
              macroDest <- inEarlierPhase $
                             schedule (Ty (TFun (Ty TSyntax) (Ty (TMacro (Ty TSyntax)))))
                               (addScope p mdef sc)
              v <- freshMacroVar
              bind b $ EIncompleteMacro v theName macroDest
              return (theName, v, macroDest)
            linkOneDecl dest $ DefineMacros macros
            linkDeclValidity vp (ScopeSet.insertAtPhase p sc scs)
        )
      , ( "example"
        , \ dest scs vp stx -> do
            p <- currentPhase
            Stx _ _ (_ :: Syntax, expr) <- mustHaveEntries stx
            exprDest <- liftIO $ newSplitCorePtr
            sch <- liftIO newSchemePtr
            linkOneDecl dest (Example (view (unSyntax . stxSrcLoc) stx) sch exprDest)
            sc <- freshScope $ T.pack $ "For example at " ++ shortShow (stxLoc stx)
            t <- inTypeBinder do
              t <- Ty . TMetaVar <$> freshMeta
              forkExpandSyntax (ExprDest t exprDest) (addScope p expr sc)
              return t
            forkGeneralizeType exprDest t sch
            linkDeclValidity vp (ScopeSet.insertAtPhase p sc scs)
        )
      , ( "import"
         -- TODO Make import spec language extensible and use bindings rather than literals
        , \dest scs vp stx -> do
            Stx stxScs loc (_ :: Syntax, toImport) <- mustHaveEntries stx
            spec <- importSpec toImport
            modExports <- getImports spec
            sc <- freshScope $ T.pack $ "For import at " ++ shortShow (stxLoc stx)
            flip forExports_ modExports $ \p x b -> inPhase p do
              imported <- addRootScope' $ addScope' (Stx stxScs loc x) sc
              addImportBinding imported b
            linkOneDecl dest (Import spec)
            linkDeclValidity vp (ScopeSet.insertUniversally sc scs)
        )
      , ( "export"
        , \dest scs vp stx -> do
            Stx _ _ (_, protoSpec) <- mustBeCons stx
            exported <- exportSpec stx protoSpec
            es <- getExports exported
            modifyState $ over expanderModuleExports $ (<> es)
            linkOneDecl dest (Export exported)
            linkDeclValidity vp scs
        )
      , ( "meta"
        , \dest scs vp stx -> do
            Stx _ _ (_ :: Syntax, subDecl) <- mustHaveEntries stx
            subDest <- liftIO newDeclTreePtr
            linkOneDecl dest (Meta subDest)
            inEarlierPhase $
              expandDeclForm subDest scs vp =<< addRootScope subDecl
        )
      ]
      where
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

        stxLoc :: Syntax -> SrcLoc
        stxLoc (Syntax (Stx _ srcloc _)) = srcloc

    exprPrims :: [(Text, Ty -> SplitCorePtr -> Syntax -> Expand ())]
    exprPrims =
      [ ( "oops"
        , \ _t _dest stx -> throwError (InternalError $ "oops" ++ show stx)
        )
      , ( "the"
        , \ t dest stx -> do
            Stx _ _ (_, ty, expr) <- mustHaveEntries stx
            tyDest <- scheduleType ty
            -- TODO add type to elaborated program? Or not?
            forkAwaitingType tyDest [TypeThenUnify dest t, TypeThenExpandExpr dest expr]
        )
      , ( "let"
        , \ t dest stx -> do
            Stx _ _ (_, b, body) <- mustHaveEntries stx
            Stx _ _ (x, def) <- mustHaveEntries b
            (sc, x', coreX) <- prepareVar x
            p <- currentPhase
            psc <- phaseRoot
            (defDest, xTy) <- inTypeBinder do
              xt <- Ty . TMetaVar <$> freshMeta
              defDest <- schedule xt def
              return (defDest, xt)
            sch <- liftIO $ newSchemePtr
            forkGeneralizeType defDest xTy sch
            bodyDest <- withLocalVarType x' coreX sch $
                          schedule t $ addScope p (addScope p body sc) psc
            linkExpr dest $ CoreLet x' coreX defDest bodyDest
        )
      , ( "flet"
        , \ t dest stx -> do
            ft <- inTypeBinder $ Ty . TMetaVar <$> freshMeta
            xt <- inTypeBinder $ Ty . TMetaVar <$> freshMeta
            rt <- inTypeBinder $ Ty . TMetaVar <$> freshMeta
            fsch <- trivialScheme ft
            xsch <- trivialScheme xt
            Stx _ _ (_, b, body) <- mustHaveEntries stx
            Stx _ _ (f, args, def) <- mustHaveEntries b
            Stx _ _ x <- mustHaveEntries args
            (fsc, f', coreF) <- prepareVar f
            (xsc, x', coreX) <- prepareVar x
            p <- currentPhase
            psc <- phaseRoot
            defDest <- inTypeBinder $
                       withLocalVarType f' coreF fsch $
                       withLocalVarType x' coreX xsch $
                       schedule rt $
                       addScope p (addScope p (addScope p def fsc) xsc) psc
            unify dest ft (Ty (TFun xt rt))
            sch <- liftIO newSchemePtr
            forkGeneralizeType defDest ft sch
            bodyDest <- withLocalVarType f' coreF sch $
                        schedule t $
                        addScope p (addScope p body fsc) psc
            linkExpr dest $ CoreLetFun f' coreF x' coreX defDest bodyDest
        )
      , ( "lambda"
        , \ t dest stx -> do
            Stx _ _ (_, arg, body) <- mustHaveEntries stx
            Stx _ _ theArg <- mustHaveEntries arg
            (sc, arg', coreArg) <- prepareVar theArg
            p <- currentPhase
            psc <- phaseRoot
            argT <- Ty . TMetaVar <$> freshMeta
            retT <- Ty . TMetaVar <$> freshMeta
            unify dest t (Ty (TFun argT retT))
            sch <- trivialScheme argT
            bodyDest <-
              withLocalVarType arg' coreArg sch $
                schedule retT $ addScope p (addScope p body sc) psc
            linkExpr dest $ CoreLam arg' coreArg bodyDest
        )
      , ( "#%app"
        , \ t dest stx -> do
            argT <- Ty . TMetaVar <$> freshMeta
            Stx _ _ (_, fun, arg) <- mustHaveEntries stx
            funDest <- schedule (Ty (TFun argT t)) fun
            argDest <- schedule argT arg
            linkExpr dest $ CoreApp funDest argDest
        )
      , ( "pure"
        , \ t dest stx -> do
            Stx _ _ (_ :: Syntax, v) <- mustHaveEntries stx
            innerT <- Ty . TMetaVar <$> freshMeta
            unify dest (Ty (TMacro innerT)) t
            argDest <- schedule innerT v
            linkExpr dest $ CorePure argDest
        )
      , ( ">>="
        , \ t dest stx -> do
            a <- Ty . TMetaVar <$> freshMeta
            b <- Ty . TMetaVar <$> freshMeta
            Stx _ _ (_, act, cont) <- mustHaveEntries stx
            actDest <- schedule (Ty (TMacro a)) act
            contDest <- schedule (Ty (TFun a (Ty (TMacro b)))) cont
            unify dest t (Ty (TMacro b))
            linkExpr dest $ CoreBind actDest contDest
        )
      , ( "syntax-error"
        , \ t dest stx -> do
            a <- Ty . TMetaVar <$> freshMeta
            unify dest t (Ty (TMacro a))
            Stx scs srcloc (_, args) <- mustBeCons stx
            Stx _ _ (msg, locs) <- mustBeCons $ Syntax $ Stx scs srcloc (List args)
            msgDest <- schedule (Ty TSyntax) msg
            locDests <- traverse (schedule (Ty TSyntax)) locs
            linkExpr dest $ CoreSyntaxError (SyntaxError locDests msgDest)
        )
      , ( "send-signal"
        , \ t dest stx -> do
            unify dest t (Ty (TMacro (Ty TUnit)))
            Stx _ _ (_ :: Syntax, sig) <- mustHaveEntries stx
            sigDest <- schedule (Ty TSignal) sig
            linkExpr dest $ CoreSendSignal sigDest
        )
      , ( "wait-signal"
        , \ t dest stx -> do
            unify dest t (Ty (TMacro (Ty TUnit)))
            Stx _ _ (_ :: Syntax, sig) <- mustHaveEntries stx
            sigDest <- schedule (Ty TSignal) sig
            linkExpr dest $ CoreWaitSignal sigDest
        )
      , ( "bound-identifier=?"
        , \ t dest stx -> do
            unify dest t (Ty (TMacro (Ty TBool)))
            Stx _ _ (_ :: Syntax, id1, id2) <- mustHaveEntries stx
            newE <- CoreIdentEq Bound <$> schedule (Ty TSyntax) id1 <*> schedule (Ty TSyntax) id2
            linkExpr dest newE
        )
      , ( "free-identifier=?"
        , \ t dest stx -> do
            unify dest t (Ty (TMacro (Ty TBool)))
            Stx _ _ (_ :: Syntax, id1, id2) <- mustHaveEntries stx
            newE <- CoreIdentEq Free <$> schedule (Ty TSyntax) id1 <*> schedule (Ty TSyntax) id2
            linkExpr dest newE
        )
      , ( "quote"
        , \ t dest stx -> do
            unify dest (Ty TSyntax) t
            Stx _ _ (_ :: Syntax, quoted) <- mustHaveEntries stx
            linkExpr dest $ CoreSyntax quoted
        )
      , ( "if"
        , \ t dest stx -> do
            Stx _ _ (_ :: Syntax, b, true, false) <- mustHaveEntries stx
            linkExpr dest =<< CoreIf <$> schedule (Ty TBool) b <*> schedule t true <*> schedule t false
        )
      , ( "ident"
        , \ t dest stx -> do
            unify dest t (Ty (TSyntax))
            Stx _ _ (_ :: Syntax, someId) <- mustHaveEntries stx
            x@(Stx _ _ _) <- mustBeIdent someId
            linkExpr dest $ CoreIdentifier x
        )
      , ( "ident-syntax"
        , \ t dest stx -> do
            unify dest t (Ty (TSyntax))
            Stx _ _ (_ :: Syntax, someId, source) <- mustHaveEntries stx
            idDest <- schedule (Ty TSyntax) someId
            sourceDest <- schedule (Ty TSyntax) source
            linkExpr dest $ CoreIdent $ ScopedIdent idDest sourceDest
        )
      , ( "empty-list-syntax"
        , \ t dest stx -> do
            unify dest t (Ty (TSyntax))
            Stx _ _ (_ :: Syntax, source) <- mustHaveEntries stx
            sourceDest <- schedule (Ty TSyntax) source
            linkExpr dest $ CoreEmpty $ ScopedEmpty sourceDest
        )
      , ( "cons-list-syntax"
        , \ t dest stx -> do
            unify dest t (Ty (TSyntax))
            Stx _ _ (_ :: Syntax, car, cdr, source) <- mustHaveEntries stx
            carDest <- schedule (Ty TSyntax) car
            cdrDest <- schedule (Ty TSyntax) cdr
            sourceDest <- schedule (Ty TSyntax) source
            linkExpr dest $ CoreCons $ ScopedCons carDest cdrDest sourceDest
        )
      , ( "list-syntax"
        , \ t dest stx -> do
            unify dest t (Ty (TSyntax))
            Stx _ _ (_ :: Syntax, list, source) <- mustHaveEntries stx
            Stx _ _ listItems <- mustHaveEntries list
            listDests <- traverse (schedule (Ty TSyntax)) listItems
            sourceDest <- schedule (Ty TSyntax) source
            linkExpr dest $ CoreList $ ScopedList listDests sourceDest
        )
      , ( "replace-loc"
        , \ t dest stx -> do
            unify dest t (Ty (TSyntax))
            Stx _ _ (_ :: Syntax, loc, valStx) <- mustHaveEntries stx
            locDest <- schedule (Ty TSyntax) loc
            valStxDest <- schedule (Ty TSyntax) valStx
            linkExpr dest $ CoreReplaceLoc locDest valStxDest
        )
      , ( "syntax-case"
        , \ t dest stx -> do
            Stx scs loc (_ :: Syntax, args) <- mustBeCons stx
            Stx _ _ (scrutinee, patterns) <- mustBeCons (Syntax (Stx scs loc (List args)))
            scrutDest <- schedule (Ty TSyntax) scrutinee
            patternDests <- traverse (mustHaveEntries >=> expandPatternCase t) patterns
            linkExpr dest $ CoreCase scrutDest patternDests
        )
      , ( "let-syntax"
        , \ t dest stx -> do
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
              schedule (Ty (TFun (Ty TSyntax) (Ty (TMacro (Ty TSyntax)))))
                (addScope (prior p) mdef psc)
            forkAwaitingMacro b v m' macroDest (ExprDest t dest) (addScope p body sc)
        )
      , ( "log"
        , \ t dest stx -> do
            unify dest (Ty (TMacro (Ty TUnit))) t
            Stx _ _ (_ :: Syntax, message) <- mustHaveEntries stx
            msgDest <- schedule (Ty TSyntax) message
            linkExpr dest $ CoreLog msgDest
        )
      , ( "case"
        , \ t dest stx -> do
            Stx _ _ (_, scrut, cases) <- mustBeConsCons stx
            a <- Ty . TMetaVar <$> freshMeta
            scrutineeDest <- schedule a scrut
            cases' <- traverse (mustHaveEntries >=> scheduleDataPattern t a) cases
            linkExpr dest $ CoreDataCase scrutineeDest cases'
        )
      ]


    expandPatternCase :: Ty -> Stx (Syntax, Syntax) -> Expand (SyntaxPattern, SplitCorePtr)
    -- TODO match case keywords hygienically
    expandPatternCase t (Stx _ _ (lhs, rhs)) = do
      p <- currentPhase
      sch <- trivialScheme (Ty TSyntax)
      case lhs of
        Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "ident")),
                               patVar])) -> do
          (sc, x', var) <- prepareVar patVar
          let rhs' = addScope p rhs sc
          rhsDest <- withLocalVarType x' var sch $ schedule t rhs'
          let patOut = SyntaxPatternIdentifier x' var
          return (patOut, rhsDest)
        Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "list")),
                               Syntax (Stx _ _ (List vars))])) -> do
          varInfo <- traverse prepareVar vars
          let rhs' = foldr (flip (addScope p)) rhs [sc | (sc, _, _) <- varInfo]
          rhsDest <- withLocalVarTypes [(var, ident, sch) | (_, ident, var) <- varInfo] $
                       schedule t rhs'
          let patOut = SyntaxPatternList [(ident, var) | (_, ident, var) <- varInfo]
          return (patOut, rhsDest)
        Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "cons")),
                               car,
                               cdr])) -> do
          (sc, car', carVar) <- prepareVar car
          (sc', cdr', cdrVar) <- prepareVar cdr
          let rhs' = addScope p (addScope p rhs sc) sc'
          rhsDest <- withLocalVarTypes [(carVar, car', sch), (cdrVar, cdr', sch)] $
                       schedule t rhs'
          let patOut = SyntaxPatternCons car' carVar cdr' cdrVar
          return (patOut, rhsDest)
        Syntax (Stx _ _ (List [])) -> do
          rhsDest <- schedule t rhs
          return (SyntaxPatternEmpty, rhsDest)
        Syntax (Stx _ _ (Id "_")) -> do
          rhsDest <- schedule t rhs
          return (SyntaxPatternAny, rhsDest)
        other ->
          throwError $ UnknownPattern other

    scheduleType :: Syntax -> Expand SplitTypePtr
    scheduleType stx = do
      dest <- liftIO newSplitTypePtr
      forkExpandType dest stx
      return dest


    addDatatype :: Ident -> Datatype -> Natural -> Expand ()
    addDatatype name dt arity = do
      name' <- addRootScope' name
      let val = EPrimTypeMacro \dest stx -> do
                  Stx _ _ (me, args) <- mustBeCons stx
                  _ <- mustBeIdent me
                  if length args /= fromIntegral arity
                    then throwError $ WrongDatatypeArity stx dt arity (length args)
                    else do
                      argDests <- traverse scheduleType args
                      linkType dest $ TDatatype dt argDests
      b <- freshBinding
      addDefinedBinding name' b
      bind b val


    addToKernel name p b =
      modifyState $ over expanderKernelExports $ addExport p name b

    addModulePrimitive :: Text -> (Syntax -> Expand ()) -> Expand ()
    addModulePrimitive name impl = do
      let val = EPrimModuleMacro impl
      b <- freshBinding
      bind b val
      addToKernel name runtime b

    addDeclPrimitive :: Text -> (DeclTreePtr -> ScopeSet -> DeclValidityPtr -> Syntax -> Expand ()) -> Expand ()
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

    addExprPrimitive :: Text -> (Ty -> SplitCorePtr -> Syntax -> Expand ()) -> Expand ()
    addExprPrimitive name impl = do
      let val = EPrimMacro impl
      b <- freshBinding
      bind b val
      addToKernel name runtime b

varPrepHelper :: Syntax -> Expand (Scope, Ident, Binding)
varPrepHelper varStx = do
  sc <- freshScope $ T.pack $ "For variable " ++ shortShow varStx
  x <- mustBeIdent varStx
  p <- currentPhase
  psc <- phaseRoot
  let x' = addScope' (addScope p x sc) psc
  b <- freshBinding
  addLocalBinding x' b
  return (sc, x', b)


prepareVar :: Syntax -> Expand (Scope, Ident, Var)
prepareVar varStx = do
  (sc, x', b) <- varPrepHelper varStx
  var <- freshVar
  bind b (EVarMacro var)
  return (sc, x', var)

prepareTypeVar :: Natural -> Syntax -> Expand (Scope, Ident)
prepareTypeVar i varStx = do
  (sc, α, b) <- varPrepHelper varStx
  bind b (ETypeVar i)
  return (sc, α)


schedule :: Ty -> Syntax -> Expand SplitCorePtr
schedule t stx@(Syntax (Stx _ loc _)) = do
  dest <- liftIO newSplitCorePtr
  saveOrigin dest loc
  forkExpandSyntax (ExprDest t dest) stx
  return dest

scheduleDataPattern ::
  Ty -> Ty ->
  Stx (Syntax, Syntax) ->
  Expand (PatternPtr, SplitCorePtr)
scheduleDataPattern exprTy scrutTy (Stx _ _ (patStx, rhsStx@(Syntax (Stx _ loc _)))) = do
  dest <- liftIO newPatternPtr
  forkExpandSyntax (PatternDest exprTy scrutTy dest) patStx
  rhsDest <- liftIO newSplitCorePtr
  saveOrigin rhsDest loc
  forkExpanderTask $ AwaitingPattern dest exprTy rhsDest rhsStx
  return (dest, rhsDest)


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


forkExpandDeclForms :: DeclTreePtr -> DeclValidityPtr -> DeclValidityPtr -> Syntax -> Expand ()
forkExpandDeclForms dest ivp ovp stx = do
  forkExpanderTask $ ExpandDeclForms dest ivp ovp stx


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
        ExprDest t d ->
          expandOneExpression t d stx
        DeclTreeDest d scs vp ->
          expandDeclForm d scs vp stx
        TypeDest d ->
          expandOneType d stx
        PatternDest exprT scrutT d ->
          expandOnePattern exprT scrutT d stx
    AwaitingType tdest after ->
      linkedType tdest >>=
      \case
        Nothing -> stillStuck tid task
        Just ty ->
          for_ after $
          \case
            TypeThenUnify dest ty' ->
              unify dest ty ty'
            TypeThenExpandExpr dest stx ->
              forkExpandSyntax (ExprDest ty dest) stx
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
    AwaitingDefn x n b defn t dest stx ->
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
              forkExpandSyntax (ExprDest t dest) stx
        Just _v -> do
          bind b $ EVarMacro x
          forkExpandSyntax (ExprDest t dest) stx
    ExpandDeclForm dest ivp ovp stx -> do
      readyYet <- view (expanderDeclValidities . at ivp) <$> getState
      case readyYet of
        Nothing ->
          stillStuck tid task
        Just scs ->
          expandDeclForm dest scs ovp (addScopes stx scs)
    ExpandDeclForms dest ivp ovp stx -> do
      readyYet <- view (expanderDeclValidities . at ivp) <$> getState
      case readyYet of
        Nothing ->
          stillStuck tid task
        Just scs ->
          expandDeclForms dest scs ovp (addScopes stx scs)
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
    ExpandVar ty eDest _ident x ->
      varType x >>=
      \case
        Nothing -> stillStuck tid task
        Just sch -> do
          specialize sch >>= unify eDest ty
          saveExprType eDest ty
          linkExpr eDest (CoreVar x)
    EstablishConstructors scs vp dt ctors -> do
      ctors' <- sequenceA <$> for ctors \(cn, ctor, argTys) -> do
                  perhapsArgs <- sequenceA <$> traverse linkedType argTys
                  pure (fmap (\ts -> (cn, ctor, ts)) perhapsArgs)
      case ctors' of
        Nothing -> stillStuck tid task
        Just ready -> do
          for_ ready \(cn, ctor, ts) ->
            addConstructor cn dt ctor ts
          linkDeclValidity vp scs
    AwaitingPattern patPtr ty dest stx -> do
      view (expanderCompletedPatterns . at patPtr) <$> getState >>=
        \case
          Nothing -> stillStuck tid task
          Just _pat -> do
            varInfo <- view (expanderPatternBinders . at patPtr) <$> getState
            case varInfo of
              Nothing -> throwError $ InternalError "Pattern info not added"
              Just vars -> do
                p <- currentPhase
                let rhs' = foldr (flip (addScope p)) stx
                             [ sc'
                             | (sc', _, _, _) <- vars
                             ]
                withLocalVarTypes
                  [ (var, varStx, t)
                  | (_sc, varStx, var, t) <- vars
                  ] $
                  expandOneExpression ty dest rhs'


  where
    laterMacro tid' b v x dest deps mdest stx = do
      localConfig <- view expanderLocal
      modifyState $
        over expanderTasks $
          ((tid', localConfig, AwaitingMacro dest (TaskAwaitMacro b v x deps mdest stx)) :)

    addConstructor ::
      Ident -> Datatype ->
      Constructor -> [Ty] ->
      Expand ()
    addConstructor name dt ctor args = do
      name' <- addRootScope' name
      let val = EConstructor ctor
      p <- currentPhase
      let info = ConstructorInfo { _ctorDatatype = dt
                                 , _ctorArguments = args
                                 }
      modifyState $
        set (expanderCurrentConstructors .
             at p . non Map.empty .
             at ctor) $
        Just info
      b <- freshBinding
      addDefinedBinding name' b
      bind b val


expandOnePattern :: Ty -> Ty -> PatternPtr -> Syntax -> Expand ()
expandOnePattern exprTy scrutTy dest stx =
  expandOneForm (PatternDest exprTy scrutTy dest) stx

expandOneType :: SplitTypePtr -> Syntax -> Expand ()
expandOneType dest stx = expandOneForm (TypeDest dest) stx

expandOneExpression :: Ty -> SplitCorePtr -> Syntax -> Expand ()
expandOneExpression t dest stx = expandOneForm (ExprDest t dest) stx

-- | Insert a function application marker with a lexical context from
-- the original expression
addApp :: (forall a . [a] -> ExprF a) -> Syntax -> [Syntax] -> Syntax
addApp ctor (Syntax (Stx scs loc _)) args =
  Syntax (Stx scs loc (ctor (app : args)))
  where
    app = Syntax (Stx scs loc (Id "#%app"))

problemContext :: MacroDest -> MacroContext
problemContext (DeclTreeDest _ _ _) = DeclarationCtx
problemContext (TypeDest _) = TypeCtx
problemContext (ExprDest _ _) = ExpressionCtx
problemContext (PatternDest _ _ _) = PatternCaseCtx

requireDeclarationCtx :: Syntax -> MacroDest -> Expand (ScopeSet, DeclTreePtr, DeclValidityPtr)
requireDeclarationCtx _ (DeclTreeDest dest scs vp) = return (scs, dest, vp)
requireDeclarationCtx stx other =
  throwError $ WrongMacroContext stx DeclarationCtx (problemContext other)

requireExpressionCtx :: Syntax -> MacroDest -> Expand (Ty, SplitCorePtr)
requireExpressionCtx _ (ExprDest ty dest) = return (ty, dest)
requireExpressionCtx stx other =
  throwError $ WrongMacroContext stx ExpressionCtx (problemContext other)

requireTypeCtx :: Syntax -> MacroDest -> Expand SplitTypePtr
requireTypeCtx _ (TypeDest dest) = return dest
requireTypeCtx stx other =
  throwError $ WrongMacroContext stx TypeCtx (problemContext other)


expandOneForm :: MacroDest -> Syntax -> Expand ()
expandOneForm prob stx
  | Just ident <- identifierHeaded stx = do
      b <- resolve =<< addRootScope ident
      v <- getEValue b
      case v of
        EPrimMacro impl -> do
          (t, dest) <- requireExpressionCtx stx prob
          impl t dest stx
          saveExprType dest t
        EConstructor ctor -> do
          ConstructorInfo args dt <- constructorInfo ctor
          DatatypeInfo arity _ <- datatypeInfo dt
          case prob of
            ExprDest t dest -> do
              argTys <- makeTypeMetas arity
              unify dest t (Ty (TDatatype dt argTys))
              args' <- for args \a -> inst (Scheme arity a) argTys
              Stx _ _ (foundName, foundArgs) <- mustBeCons stx
              _ <- mustBeIdent foundName
              argDests <-
                if length foundArgs /= length args'
                  then throwError $
                       WrongArgCount stx ctor (length args') (length foundArgs)
                  else for (zip args' foundArgs) (uncurry schedule)
              linkExpr dest (CoreCtor ctor argDests)
              saveExprType dest t
            PatternDest _exprTy patTy dest -> do
              Stx _ loc (_cname, patVars) <- mustBeCons stx
              tyArgs <- makeTypeMetas arity
              argTypes <- for args \ a -> do
                            t <- inst (Scheme arity a) tyArgs
                            trivialScheme t
              unify loc (Ty (TDatatype dt tyArgs)) patTy
              if length patVars /= length argTypes
                then throwError $ WrongArgCount stx ctor (length argTypes) (length patVars)
                else do
                  varInfo <- traverse prepareVar patVars
                  modifyState $
                    set (expanderPatternBinders . at dest) $
                    Just [ (sc, name, x, t)
                         | ((sc, name, x), t) <- zip varInfo argTypes
                         ]
                  linkPattern dest $
                    ConstructorPattern ctor [ (varStx, var)
                                            | (_, varStx, var) <- varInfo
                                            ]
            other ->
              throwError $ WrongMacroContext stx ExpressionCtx (problemContext other)
        EPrimModuleMacro _ ->
          throwError $ WrongMacroContext stx (problemContext prob) ModuleCtx
        EPrimDeclMacro impl -> do
          (scs, dest, vp) <- requireDeclarationCtx stx prob
          impl dest scs vp stx
        EPrimTypeMacro impl -> do
          dest <- requireTypeCtx stx prob
          impl dest stx
        EVarMacro var -> do
          (t, dest) <- requireExpressionCtx stx prob
          case syntaxE stx of
            Id _ ->
              forkExpandVar t dest stx var
            String _ -> error "Impossible - string not ident"
            Sig _ -> error "Impossible - signal not ident"
            Bool _ -> error "Impossible - boolean not ident"
            List xs -> expandOneExpression t dest (addApp List stx xs)
        ETypeVar i -> do
          dest <- requireTypeCtx stx prob
          linkType dest (TSchemaVar i)
        EIncompleteDefn x n d -> do
          (t, dest) <- requireExpressionCtx stx prob
          forkAwaitingDefn x n b d t dest stx
        EIncompleteMacro transformerName sourceIdent mdest ->
          forkAwaitingMacro b transformerName sourceIdent mdest prob stx
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
                    Left (sig, kont) ->
                      forkAwaitingSignal prob sig kont
                    Right expanded ->
                      case expanded of
                        ValueSyntax expansionResult ->
                          forkExpandSyntax prob (flipScope p expansionResult stepScope)
                        other -> throwError $ ValueNotSyntax other
                other ->
                  throwError $ ValueNotMacro other
            Nothing ->
              throwError $ InternalError $
              "No transformer yet created for " ++ shortShow ident ++
              " (" ++ show transformerName ++ ") at phase " ++ shortShow p
            Just other -> throwError $ ValueNotMacro other
  | otherwise =
    case prob of
      DeclTreeDest _ _ _ ->
        throwError $ InternalError "All declarations should be identifier-headed"
      TypeDest _dest ->
        throwError $ NotValidType stx
      PatternDest _ _ _ ->
        throwError $ InternalError "All patterns should be identifier-headed"
      ExprDest t dest ->
        case syntaxE stx of
          List xs -> expandOneExpression t dest (addApp List stx xs)
          Sig s -> do
            unify dest (Ty TSignal) t
            expandLiteralSignal dest s
            saveExprType dest t
          Bool b -> do
            unify dest (Ty TBool) t
            linkExpr dest (CoreBool b)
            saveExprType dest t
          String s -> expandLiteralString dest s
          Id _ -> error "Impossible happened - identifiers are identifier-headed!"


expandDeclForm :: DeclTreePtr -> ScopeSet -> DeclValidityPtr -> Syntax -> Expand ()
expandDeclForm dest scs vp stx =
  expandOneForm (DeclTreeDest dest scs vp) stx

expandDeclForms :: DeclTreePtr -> ScopeSet -> DeclValidityPtr -> Syntax -> Expand ()
expandDeclForms dest scs vp (Syntax (Stx _ _ (List []))) = do
  linkDeclTree dest DeclTreeLeaf
  linkDeclValidity vp scs
expandDeclForms dest scs vp (Syntax (Stx stxScs loc (List (d:ds)))) = do
  carDest <- liftIO $ newDeclTreePtr
  cdrDest <- liftIO $ newDeclTreePtr
  carValidityPtr <- newDeclValidityPtr
  linkDeclTree dest (DeclTreeBranch carDest cdrDest)
  forkExpandDeclForms cdrDest carValidityPtr vp
    (Syntax (Stx stxScs loc (List ds)))
  expandDeclForm carDest scs carValidityPtr =<< addRootScope d
expandDeclForms _dest _scs _vp _stx =
  error "TODO real error message - malformed module body"


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
      return $ Right $ ValueBool $
        view stxValue id1 == view stxValue id2 &&
        view stxScopeSet id1 == view stxScopeSet id2
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

class UnificationErrorBlame a where
  getBlameLoc :: a -> Expand (Maybe SrcLoc)

instance UnificationErrorBlame SrcLoc where
  getBlameLoc = pure . pure

instance UnificationErrorBlame SplitCorePtr where
  getBlameLoc ptr = view (expanderOriginLocations . at ptr) <$> getState

-- The expected type is first, the received is second
unify :: UnificationErrorBlame blame => blame -> Ty -> Ty -> Expand ()
unify blame t1 t2 = do
  t1' <- normType t1
  t2' <- normType t2
  unify' (unTy t1') (unTy t2')

  where
    unify' :: TyF Ty -> TyF Ty -> Expand ()
    -- Rigid-rigid
    unify' TBool TBool = pure ()
    unify' TUnit TUnit = pure ()
    unify' TSyntax TSyntax = pure ()
    unify' TSignal TSignal = pure ()
    unify' (TFun a c) (TFun b d) = unify blame b a >> unify blame c d
    unify' (TMacro a) (TMacro b) = unify blame a b
    unify' (TDatatype dt1 args1) (TDatatype dt2 args2)
      | dt1 == dt2 = traverse_ (uncurry (unify blame)) (zip args1 args2)

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
    unify' expected received = do
      loc <- getBlameLoc blame
      throwError $ TypeMismatch loc (Ty expected) (Ty received)
