{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
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
  , mkInitContext
  , initializeKernel
  , initializeLanguage
  , currentPhase
  , expandEval
  , ExpansionErr(..)
  , expanderBindingTable
  , expanderWorld
  , getState
  , addRootScope
  , addModuleScope
  ) where

import Control.Lens hiding (Context(..), List, children)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Foldable
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
import Module
import ModuleName
import Parser
import Phase
import Pretty
import Scope
import ScopeCheck
import ScopeSet (ScopeSet)
import Signals
import ShortShow
import SplitCore
import Syntax
import Syntax.SrcLoc
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
    let theModule = Module { _moduleName = modName
                           , _moduleImports = noImports
                           , _moduleBody = body
                           , _moduleExports = noExports
                           }
    return $ Expanded theModule




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
         Nothing -> do
           (m, es) <- inPhase runtime $ loadModuleFile modName
           return (m, es)
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
  return (shift i es)

-- | Evaluate an expanded module at the current expansion phase,
-- recursively loading its run-time dependencies.
evalMod :: CompleteModule -> Expand [EvalResult]
evalMod (KernelModule _) =
  -- Builtins go here, suitably shifted. There are no built-in values
  -- yet, only built-in syntax, but this may change.
  return []
evalMod (Expanded em) = snd <$> runWriterT (traverse_ evalDecl (view moduleBody em))
  where
    evalDecl (CompleteDecl d) =
      case d of
        Define x n e -> do
          val <- lift $ expandEval (eval e)
          p <- lift currentPhase
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

bindingTable :: Expand BindingTable
bindingTable = view expanderBindingTable <$> getState

addBinding :: Ident -> Binding -> BindingInfo SrcLoc -> Expand ()
addBinding (Stx scs _ name) b info = do
  modifyState $ over (expanderBindingTable . at name) $
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
  allBindings <- bindingTable
  p <- currentPhase
  let namesMatch = view (at x . non []) allBindings
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
            x <- flip (addScope p) sc <$> mustBeIdent varStx
            b <- freshBinding
            addDefinedBinding x b
            var <- freshVar
            exprDest <- liftIO $ newSplitCorePtr
            bind b (EIncompleteDefn var x exprDest)
            linkDecl dest (Define x var exprDest)
            forkExpandSyntax (ExprDest exprDest) expr
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
              macroDest <- inEarlierPhase $ do
                psc <- phaseRoot
                schedule (addScope p (addScope (prior p) mdef psc) sc)
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
            Stx _ _ (_ :: Syntax, ident) <- mustHaveEntries stx
            exported@(Stx _ _ x) <- mustBeIdent ident
            p <- currentPhase
            b <- resolve exported
            modifyState $ over expanderModuleExports $ addExport p x b
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


    exprPrims :: [(Text, SplitCorePtr -> Syntax -> Expand ())]
    exprPrims =
      [ ( "oops"
        , \ _ stx -> throwError (InternalError $ "oops" ++ show stx)
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
            Stx _ _ (_ :: Syntax, macro, body) <- mustHaveEntries stx
            Stx _ _ (mName, mdef) <- mustHaveEntries macro
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
      sc <- freshScope
      x <- mustBeIdent varStx
      p <- currentPhase
      psc <- phaseRoot
      let x' = addScope' (addScope p x sc) psc
      b <- freshBinding
      addLocalBinding x' b
      var <- freshVar
      bind b (EVarMacro var)
      return (sc, x', var)


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
    ScopeCheckTask splitCore -> scopeCheckExpand localData splitCore
  where
    laterMacro tid' b v x dest deps mdest stx = do
      localConfig <- view expanderLocal
      modifyState $
        over expanderTasks $
          ((tid', localConfig, AwaitingMacro dest (TaskAwaitMacro b v x deps mdest stx)) :)



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
        EIncompleteMacro transformerName sourceIdent mdest -> do
          forkAwaitingMacro b transformerName sourceIdent mdest dest stx
        EIncompleteDefn x n d ->
          forkAwaitingDefn x n b d dest stx
        EUserMacro transformerName -> do
          stepScope <- freshScope
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
        EUserMacro transformerName -> do
          stepScope <- freshScope
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

type NewScopeCheckTask = (Context, SplitCore)

scopeCheckExpand :: ExpanderLocal -> SplitCore -> Expand ()
scopeCheckExpand localState splitCore = do
  phase <- currentPhase
  let ctx = view expanderContext localState
  root <-
    case getRoot splitCore of
      Nothing -> fail "internal error"
      Just rt -> pure rt
  let
    recursiveCase ::
      Phase ->
      SplitCorePtr ->
      ScopeCheckT (Writer [NewScopeCheckTask]) ()
    recursiveCase _ splitCorePtr = do
      env <- ask -- possibly-expanded
      case subtree splitCore splitCorePtr of
        Nothing -> fail "Malformed splitcore!"
        Just splitCoreSubtree -> lift $ tell [(env, splitCoreSubtree)]
  let errorOr =
        runWriter $
          runScopeCheckT ctx $
            scopeCheckCoreF recursiveCase phase root
  case errorOr of
    (Left _, _) -> fail "Scope check error!"
    (Right _, tasks) ->
      forM_ tasks $ \(newCtxt, splitCoreSubtree) ->
        -- Add newly-bound variables to the new task
        localForkExpanderTask
          (localState & expanderContext %~ (<> newCtxt))
          (ScopeCheckTask splitCoreSubtree)
