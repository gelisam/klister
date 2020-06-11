-- TODO next step is add prisms for Type
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
    expandExpr
  , expandModule
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
  , completely
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
import Numeric.Natural
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Traversable
import System.Directory

import Binding
import Control.Lens.IORef
import Core
import Datatype
import qualified Env
import Evaluator
import qualified Expander.Primitives as Prims
import Expander.DeclScope
import Expander.Syntax
import Expander.Monad
import Expander.TC
import Module
import ModuleName
import Parser
import Phase
import Pretty
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
  typePatterns <- view expanderCompletedTypePatterns <$> getState
  return $ SplitCore { _splitCoreRoot = dest
                     , _splitCoreDescendants = children
                     , _splitCorePatterns = patterns
                     , _splitCoreTypePatterns = typePatterns
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
  modifyState $ set expanderDefTypes mempty
  local (set (expanderLocal . expanderModuleName) thisMod) do
    lang <- mustBeModName (view moduleLanguage src)
    initializeLanguage lang
    declTreeDest <- newDeclTreePtr
    outScopesDest <- newDeclOutputScopesPtr
    modifyState $ set expanderModuleTop $ Just declTreeDest
    decls <- addModuleScope (view moduleContents src)
    completely do
      expandDeclForms declTreeDest mempty outScopesDest decls
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
         startExports <- view expanderModuleExports <$> getState
         modifyState $ set expanderModuleExports noExports
         m <- expandModule modName stx
         es <- view expanderModuleExports <$> getState
         modifyState $ set expanderModuleExports startExports

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
           let es = fromMaybe noExports $ view (worldExports . at modName) world
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
    sc <- freshScope $ T.pack $ "For module-phase " ++ shortShow modName ++ "-" ++ shortShow p
    let syntaxScopeSets :: Traversal' Syntax ScopeSet
        syntaxScopeSets f (Syntax (Stx scopeSet srcLoc expr))
          = Syntax <$> ( Stx
                     <$> f scopeSet
                     <*> pure srcLoc
                     <*> traverseOf exprScopeSets f expr
                       )
        exprScopeSets :: Traversal' (ExprF Syntax) ScopeSet
        exprScopeSets = _List . each . syntaxScopeSets
        syntaxErrorCores :: Traversal' (SyntaxError Core) Core
        syntaxErrorCores f (SyntaxError cores core)
            = SyntaxError
          <$> traverseOf each f cores
          <*> f core
        scopedIdentCores :: Traversal' (ScopedIdent Core) Core
        scopedIdentCores f (ScopedIdent core1 core2)
            = ScopedIdent
          <$> f core1
          <*> f core2
        scopedEmptyCores :: Traversal' (ScopedEmpty Core) Core
        scopedEmptyCores f (ScopedEmpty core)
            = ScopedEmpty
          <$> f core
        scopedConsCores :: Traversal' (ScopedCons Core) Core
        scopedConsCores f (ScopedCons core1 core2 core3)
            = ScopedCons
          <$> f core1
          <*> f core2
          <*> f core3
        scopedListCores :: Traversal' (ScopedList Core) Core
        scopedListCores f (ScopedList cores core)
            = ScopedList
          <$> traverseOf each f cores
          <*> f core
        coreSyntaxes :: Traversal' Core Syntax
        coreSyntaxes f (Core coreF) = Core <$> case coreF of
          CoreVar var
            -> CoreVar
           <$> pure var
          CoreLet ident var core1 core2
            -> CoreLet
           <$> pure ident
           <*> pure var
           <*> traverseOf coreSyntaxes f core1
           <*> traverseOf coreSyntaxes f core2
          CoreLetFun ident1 var1 ident2 var2 core1 core2
            -> CoreLetFun
           <$> pure ident1
           <*> pure var1
           <*> pure ident2
           <*> pure var2
           <*> traverseOf coreSyntaxes f core1
           <*> traverseOf coreSyntaxes f core2
          CoreLam ident var core
            -> CoreLam
           <$> pure ident
           <*> pure var
           <*> traverseOf coreSyntaxes f core
          CoreApp core1 core2
            -> CoreApp
           <$> traverseOf coreSyntaxes f core1
           <*> traverseOf coreSyntaxes f core2
          CoreCtor constructor cores
            -> CoreCtor
           <$> pure constructor
           <*> traverseOf (each . coreSyntaxes) f cores
          CoreDataCase srcLoc core ctors
            -> CoreDataCase
           <$> pure srcLoc
           <*> traverseOf coreSyntaxes f core
           <*> traverseOf (each . _2 . coreSyntaxes) f ctors
          CoreError core
            -> CoreError
           <$> traverseOf coreSyntaxes f core
          CorePure core
            -> CorePure
           <$> traverseOf coreSyntaxes f core
          CoreBind core1 core2
            -> CoreBind
           <$> traverseOf coreSyntaxes f core1
           <*> traverseOf coreSyntaxes f core2
          CoreSyntaxError syntaxError
            -> CoreSyntaxError
           <$> traverseOf (syntaxErrorCores . coreSyntaxes) f  syntaxError
          CoreSendSignal core
            -> CoreSendSignal
           <$> traverseOf coreSyntaxes f core
          CoreWaitSignal core
            -> CoreWaitSignal
           <$> traverseOf coreSyntaxes f core
          CoreIdentEq howEq core1 core2
            -> CoreIdentEq
           <$> pure howEq
           <*> traverseOf coreSyntaxes f core1
           <*> traverseOf coreSyntaxes f core2
          CoreLog core
            -> CoreLog
           <$> traverseOf coreSyntaxes f core
          CoreMakeIntroducer
            -> pure CoreMakeIntroducer
          CoreWhichProblem
            -> pure CoreWhichProblem
          CoreSyntax syntax
            -> CoreSyntax
           <$> f syntax
          CoreCase srcLoc core clauses
            -> CoreCase
           <$> pure srcLoc
           <*> traverseOf coreSyntaxes f core
           <*> traverseOf (each . _2 . coreSyntaxes) f clauses
          CoreIdentifier ident
            -> CoreIdentifier
           <$> pure ident
          CoreSignal signal
            -> CoreSignal
           <$> pure signal
          CoreIdent scopedIdent
            -> CoreIdent
           <$> traverseOf (scopedIdentCores . coreSyntaxes) f scopedIdent
          CoreEmpty scopedEmpty
            -> CoreEmpty
           <$> traverseOf (scopedEmptyCores . coreSyntaxes) f scopedEmpty
          CoreCons scopedCons
            -> CoreCons
           <$> traverseOf (scopedConsCores . coreSyntaxes) f scopedCons
          CoreList scopedList
            -> CoreList
           <$> traverseOf (scopedListCores . coreSyntaxes) f scopedList
          CoreReplaceLoc core1 core2
            -> CoreReplaceLoc
           <$> traverseOf coreSyntaxes f core1
           <*> traverseOf coreSyntaxes f core2
          CoreTypeCase srcLoc core clauses
            -> CoreTypeCase
           <$> pure srcLoc
           <*> traverseOf coreSyntaxes f core
           <*> traverseOf (each . _2 . coreSyntaxes) f clauses
        declSyntaxes :: Traversal' (Decl Ty (Scheme Ty) [CompleteDecl] Core) Syntax
        declSyntaxes f = \case
          Define ident var scheme core
            -> Define
           <$> pure ident
           <*> pure var
           <*> pure scheme
           <*> traverseOf coreSyntaxes f core
          DefineMacros macros
            -> DefineMacros
           <$> traverseOf (each . _3 . coreSyntaxes) f macros
          Meta decls
            -> Meta
           <$> traverseOf (each . completeDeclSyntaxes) f decls
          Example srcLoc scheme core
            -> Example srcLoc scheme
           <$> traverseOf coreSyntaxes f core
          Import importSpec
            -> Import
           <$> pure importSpec
          Export exportSpec
            -> Export
           <$> pure exportSpec
          Data ident internalName arity ctors
            -> Data
           <$> pure ident
           <*> pure internalName
           <*> pure arity
           <*> pure ctors
        completeDeclSyntaxes :: Traversal' CompleteDecl Syntax
        completeDeclSyntaxes = completeDecl . declSyntaxes
        moduleSyntaxes :: Traversal' (Module [] CompleteDecl) Syntax
        moduleSyntaxes = moduleBody . each . completeDeclSyntaxes
        bindingTableScopeSets :: Traversal' BindingTable ScopeSet
        bindingTableScopeSets = bindings . each . each . _1
        completeModuleScopeSets :: Traversal' CompleteModule ScopeSet
        completeModuleScopeSets = _Expanded
                                . beside (moduleSyntaxes . syntaxScopeSets)
                                         bindingTableScopeSets
    let m'' = over completeModuleScopeSets (ScopeSet.insertUniversally sc) m'
    evalResults <- inPhase p $ evalMod m''
    modifyState $
      set (expanderWorld . worldEvaluated . at modName)
          (Just evalResults)
    let bs = getModuleBindings m''
    modifyState $ over expanderGlobalBindingTable $ (<> bs)
  return (shift i es)
  where getModuleBindings (Expanded _ bs) = bs
        getModuleBindings (KernelModule _) = mempty

-- | Evaluate an expanded module at the current expansion phase,
-- recursively loading its run-time dependencies.
evalMod :: CompleteModule -> Expand [EvalResult]
evalMod (KernelModule _) = do
  -- Builtins go here, suitably shifted. There are no built-in values
  -- yet, only built-in syntax and datatypes, but this may change.
  p <- currentPhase
  dts <- view expanderKernelDatatypes <$> getState
  modifyState $
    over (expanderWorld . worldDatatypes . at p . non Map.empty) $
    Map.union dts
  ctors <- view expanderKernelConstructors <$> getState
  modifyState $
    over (expanderWorld . worldConstructors . at p . non Map.empty) $
    Map.union ctors

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
            over (expanderWorld . worldTypeContexts . at p) $
            Just . maybe (Env.singleton n x ptr) (Env.insert n x ptr)
          lift $ modifyState $
            over (expanderWorld . worldEnvironments . at p) $
            Just . maybe (Env.singleton n x val) (Env.insert n x val)
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
              over (expanderWorld . worldTransformerEnvironments . at p) $
              Just . maybe (Env.singleton n x v) (Env.insert n x v)
        Meta decls -> do
          ((), out) <- lift $ inEarlierPhase (runWriterT $ traverse_ evalDecl decls)
          tell out
        Import spec -> lift $ getImports spec >> pure () -- for side effect of evaluating module
        Export _ -> pure ()




getEValue :: Binding -> Expand EValue
getEValue b = do
  ExpansionEnv env <- view expanderExpansionEnv <$> getState
  case Map.lookup b env of
    Just v -> return v
    Nothing -> throwError (InternalError ("No such binding: " ++ show b))


visibleBindings :: Expand BindingTable
visibleBindings = do
  globals <- view expanderGlobalBindingTable <$> getState
  locals <- view expanderCurrentBindingTable <$> getState
  return (globals <> locals)




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


initializeKernel :: Expand ()
initializeKernel = do
  traverse_ (uncurry addExprPrimitive) exprPrims
  traverse_ (uncurry addModulePrimitive) modPrims
  traverse_ (uncurry addDeclPrimitive) declPrims
  traverse_ (uncurry addTypePrimitive) typePrims
  traverse_ (uncurry addPatternPrimitive) patternPrims
  traverse_ addDatatypePrimitive datatypePrims
  addUniversalPrimitive "with-unknown-type" Prims.makeLocalType


  where
    typePrims :: [(Text, (SplitTypePtr -> Syntax -> Expand (), TypePatternPtr -> Syntax -> Expand ()))]
    typePrims =
      [ ("Syntax", Prims.baseType TSyntax)
      , ("Signal", Prims.baseType TSignal)
      , ("->", Prims.arrowType)
      , ("Macro", Prims.macroType)
      , ("Type", Prims.baseType TType)
      ]

    datatypePrims :: [(Text, Natural, [(Text, [Ty])])]
    datatypePrims =
      [ ("ScopeAction", 0, [("flip", []), ("add", []), ("remove", [])])
      , ("Unit", 0, [("unit", [])])
      , ("Bool", 0, [("true", []), ("false", [])])
      , ("Problem", 0, [("declaration", []), ("expression", [Ty TType]), ("type", []), ("pattern", [])])
      , ("Maybe", 1, [("nothing", []), ("just", [Ty $ TSchemaVar 0])])
      ]

    modPrims :: [(Text, Syntax -> Expand ())]
    modPrims = [("#%module", Prims.makeModule expandDeclForms)]

    declPrims :: [(Text, DeclTreePtr -> DeclOutputScopesPtr -> Syntax -> Expand ())]
    declPrims =
      [ ("define", Prims.define)
      , ("datatype", Prims.datatype)
      , ("define-macros", Prims.defineMacros)
      , ("example", Prims.example)
      , ("import", primImportModule)
      , ("export", primExport)
      , ("meta", Prims.meta expandDeclForms)
      , ("group", Prims.group expandDeclForms)
      ]

    exprPrims :: [(Text, Ty -> SplitCorePtr -> Syntax -> Expand ())]
    exprPrims =
      [ ("oops", Prims.oops)
      , ("error", Prims.err)
      , ("the", Prims.the)
      , ("let", Prims.letExpr)
      , ("flet", Prims.flet)
      , ("lambda", Prims.lambda)
      , ("#%app", Prims.app)
      , ("pure", Prims.pureMacro)
      , (">>=", Prims.bindMacro)
      , ("syntax-error", Prims.syntaxError)
      , ("send-signal", Prims.sendSignal)
      , ("wait-signal", Prims.waitSignal)
      , ("bound-identifier=?", Prims.identEqual Bound)
      , ("free-identifier=?", Prims.identEqual Free)
      , ("quote", Prims.quote)
      , ("ident", Prims.ident)
      , ("ident-syntax", Prims.identSyntax)
      , ("empty-list-syntax", Prims.emptyListSyntax)
      , ("cons-list-syntax", Prims.consListSyntax)
      , ("list-syntax", Prims.listSyntax)
      , ("replace-loc", Prims.replaceLoc)
      , ("syntax-case", Prims.syntaxCase)
      , ("let-syntax", Prims.letSyntax)
      , ("log", Prims.log)
      , ("make-introducer", Prims.makeIntroducer)
      , ("which-problem", Prims.whichProblem)
      , ("case", Prims.dataCase)
      , ("type-case", Prims.typeCase)
      ]

    patternPrims :: [(Text, Either (Ty, Ty, PatternPtr) (Ty, TypePatternPtr) -> Syntax -> Expand ())]
    patternPrims = [("else", Prims.elsePattern)]

    addToKernel name p b =
      modifyState $ over expanderKernelExports $ addExport p name b

    addDatatypePrimitive :: (Text, Natural, [(Text, [Ty])]) -> Expand ()
    addDatatypePrimitive (name, arity, ctors) = do
      let dn = DatatypeName name
      let dt = Datatype
                 { _datatypeModule = KernelName kernelName
                 , _datatypeName = dn
                 }
      let tyImpl =
             \dest stx -> do
               Stx _ _ (me, args) <- mustBeCons stx
               _ <- mustBeIdent me
               if length args /= fromIntegral arity
                 then throwError $ WrongDatatypeArity stx dt arity (length args)
                 else do
                   argDests <- traverse scheduleType args
                   linkType dest $ TDatatype dt argDests
          patImpl =
            \dest stx -> do
              Stx _ _ (me, args) <- mustBeCons stx
              _ <- mustBeIdent me
              if length args /= fromIntegral arity
                then throwError $ WrongDatatypeArity stx dt arity (length args)
                else do
                  varInfo <- traverse Prims.prepareVar args
                  sch <- trivialScheme $ Ty TType
                  modifyState $
                    set (expanderPatternBinders . at (Right dest)) $
                    Just [ (sc, n, x, sch)
                         | (sc, n, x) <- varInfo
                         ]
                  linkTypePattern dest $
                    TypePattern $ TDatatype dt [(varStx, var) | (_, varStx, var) <- varInfo]
      let val = EPrimTypeMacro tyImpl patImpl
      b <- freshBinding
      bind b val
      addToKernel name runtime b
      ctors' <- for ctors \(ctorName, args) -> do
        let cn = ConstructorName ctorName
        let ctor = Constructor { _constructorModule = KernelName kernelName
                               , _constructorName = cn
                               }
        let cInfo = ConstructorInfo { _ctorArguments = args
                                    , _ctorDatatype = dt
                                    }
        modifyState $
          over expanderKernelConstructors $
          Map.insert ctor cInfo
        cb <- freshBinding
        bind cb $ EConstructor ctor
        addToKernel ctorName runtime cb
        pure ctor

      let info =
            DatatypeInfo
            { _datatypeArity = arity
            , _datatypeConstructors = ctors'
            }
      modifyState $
        over expanderKernelDatatypes $
        Map.insert dt info


    addPatternPrimitive ::
      Text -> (Either (Ty, Ty, PatternPtr) (Ty, TypePatternPtr) -> Syntax -> Expand ()) -> Expand ()
    addPatternPrimitive name impl = do
      let val = EPrimPatternMacro impl
      b <- freshBinding
      bind b val
      addToKernel name runtime b

    addModulePrimitive :: Text -> (Syntax -> Expand ()) -> Expand ()
    addModulePrimitive name impl = do
      let val = EPrimModuleMacro impl
      b <- freshBinding
      bind b val
      addToKernel name runtime b

    addDeclPrimitive :: Text -> (DeclTreePtr -> DeclOutputScopesPtr -> Syntax -> Expand ()) -> Expand ()
    addDeclPrimitive name impl = do
      let val = EPrimDeclMacro impl
      b <- freshBinding
      -- FIXME primitive scope:
      bind b val
      addToKernel name runtime b

    addTypePrimitive ::
      Text ->
      (SplitTypePtr -> Syntax -> Expand (), TypePatternPtr -> Syntax -> Expand ()) ->
      Expand ()
    addTypePrimitive name (implT, implP) = do
      let val = EPrimTypeMacro implT implP
      b <- freshBinding
      bind b val
      addToKernel name runtime b

    addExprPrimitive :: Text -> (Ty -> SplitCorePtr -> Syntax -> Expand ()) -> Expand ()
    addExprPrimitive name impl = do
      let val = EPrimExprMacro impl
      b <- freshBinding
      bind b val
      addToKernel name runtime b

    addUniversalPrimitive :: Text -> (MacroDest -> Syntax -> Expand ()) -> Expand ()
    addUniversalPrimitive name impl = do
      let val = EPrimUniversalMacro impl
      b <- freshBinding
      bind b val
      addToKernel name runtime b


-- TODO Make import spec language extensible and use bindings rather
-- than literals
primImportModule :: DeclTreePtr -> DeclOutputScopesPtr -> Syntax -> Expand ()
primImportModule dest outScopesDest importStx = do
  Stx scs loc (_ :: Syntax, toImport) <- mustHaveEntries importStx
  spec <- importSpec toImport
  modExports <- getImports spec
  sc <- freshScope $ T.pack $ "For import at " ++ shortShow (stxLoc importStx)
  flip forExports_ modExports $ \p x b -> inPhase p do
    imported <- addModuleScope =<< addRootScope' (addScope' (Stx scs loc x) sc)
    addImportBinding imported b
  linkOneDecl dest (Import spec)
  linkDeclOutputScopes outScopesDest (ScopeSet.singleUniversalScope sc)
  where
    importSpec :: Syntax -> Expand ImportSpec
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
    importSpec modStx = ImportModule <$> mustBeModName modStx
    getRename s = do
      Stx _ _ (old', new') <- mustHaveEntries s
      old <- mustBeIdent old'
      new <- mustBeIdent new'
      return (old, new)

primExport :: DeclTreePtr -> DeclOutputScopesPtr -> Syntax -> Expand ()
primExport dest outScopesDest stx = do
  Stx _ _ (_, protoSpec) <- mustBeCons stx
  exported <- exportSpec stx protoSpec
  es <- getExports exported
  modifyState $ over expanderModuleExports $ (<> es)
  linkOneDecl dest (Export exported)
  linkDeclOutputScopes outScopesDest mempty
  where
    exportSpec :: Syntax -> [Syntax] -> Expand ExportSpec
    exportSpec blame elts
      | [Syntax (Stx scs' srcloc'  (List ((getIdent -> Just (Stx _ _ kw)) : args)))] <- elts =
          case kw of
            "rename" ->
              case args of
                (rens : more) -> do
                  pairs <- getRenames blame rens
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


    getIdent (Syntax (Stx scs loc (Id x))) = pure (Stx scs loc x)
    getIdent _ = empty

    getRenames _blame (syntaxE -> List rens) =
      for rens $ \renStx -> do
        Stx _ _ (x, y) <- mustHaveEntries renStx
        Stx _ _ x' <- mustBeIdent x
        Stx _ _ y' <- mustBeIdent y
        pure (x', y')
    getRenames blame _ = throwError $ NotExportSpec blame

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
        then return ()
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
        DeclTreeDest d outScopesDest ->
          expandDeclForm d outScopesDest stx
        TypeDest d ->
          expandOneType d stx
        PatternDest exprT scrutT d ->
          expandOnePattern exprT scrutT d stx
        TypePatternDest exprT d ->
          expandOneTypePattern exprT d stx
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
          let result = primitiveCtor "unit" []
          forkContinueMacroAction dest result kont
    AwaitingTypeCase loc dest ty env cases kont -> do
      Ty t <- normType ty
      case t of
        TMetaVar ptr' ->
          -- Always wait on the canonical representative
          case ty of
            Ty (TMetaVar ptr) | ptr == ptr' -> stillStuck tid task
            _ -> forkAwaitingTypeCase loc dest (Ty (TMetaVar ptr')) env cases kont
        other -> do
          selectedBranch <- expandEval $ withEnv env $ doTypeCase loc (Ty other) cases
          case selectedBranch of
            ValueMacroAction nextStep -> do
              forkInterpretMacroAction dest nextStep kont
            otherVal -> do
              expandEval $ evalErrorType "macro action" otherVal
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
    ExpandDeclForms dest earlierScopeSet waitingOn outScopesDest stx -> do
      -- The scopes in waitingOn (from the preceding declaration) haven't yet
      -- been added to stx, while those in earlierScopeSet (from the
      -- declarations before that) have. The scopes from both, plus the scopes
      -- introduced by the declaration forms in stx, must all eventually be
      -- placed in outScopesDest so that the code which isn't part of this
      -- declaration group can have access to those declarations.
      readyYet <- view (expanderDeclOutputScopes . at waitingOn) <$> getState
      case readyYet of
        Nothing ->
          stillStuck tid task
        Just newScopeSet ->
          expandDeclForms dest (earlierScopeSet <> newScopeSet) outScopesDest (addScopes stx newScopeSet)
    InterpretMacroAction dest act outerKont ->
      interpretMacroAction dest act >>= \case
        StuckOnSignal signal innerKont ->
          forkAwaitingSignal dest signal (innerKont ++ outerKont)
        StuckOnType loc ty env cases innerKont ->
          forkAwaitingTypeCase loc dest ty env cases (innerKont ++ outerKont)
        Done value -> do
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
    EstablishConstructors scs outScopesDest dt ctors -> do
      ctors' <- sequenceA <$> for ctors \(cn, ctor, argTys) -> do
                  perhapsArgs <- sequenceA <$> traverse linkedType argTys
                  pure (fmap (\ts -> (cn, ctor, ts)) perhapsArgs)
      case ctors' of
        Nothing -> stillStuck tid task
        Just ready -> do
          for_ ready \(cn, ctor, ts) ->
            addConstructor cn dt ctor ts
          linkDeclOutputScopes outScopesDest scs
    AwaitingPattern patPtr ty dest stx -> do
      ready <-
        case patPtr of
          Left pptr -> isJust . view (expanderCompletedPatterns . at pptr) <$> getState
          Right tptr -> isJust . view (expanderCompletedTypePatterns . at tptr) <$> getState
      if (not ready)
        then stillStuck tid task
        else do
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

expandOneTypePattern :: Ty -> TypePatternPtr -> Syntax -> Expand ()
expandOneTypePattern exprTy dest stx =
  expandOneForm (TypePatternDest exprTy dest) stx


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
problemContext (DeclTreeDest {}) = DeclarationCtx
problemContext (TypeDest {}) = TypeCtx
problemContext (ExprDest {}) = ExpressionCtx
problemContext (PatternDest {}) = PatternCaseCtx
problemContext (TypePatternDest {}) = TypePatternCaseCtx

requireDeclarationCtx :: Syntax -> MacroDest -> Expand (DeclTreePtr, DeclOutputScopesPtr)
requireDeclarationCtx _ (DeclTreeDest dest outScopesDest) = return (dest, outScopesDest)
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

requirePatternCtx :: Syntax -> MacroDest -> Expand (Either (Ty, Ty, PatternPtr) (Ty, TypePatternPtr))
requirePatternCtx _ (PatternDest exprTy scrutTy dest) =
  return $ Left (exprTy, scrutTy, dest)
requirePatternCtx _ (TypePatternDest exprTy dest) =
  return $ Right (exprTy, dest)
requirePatternCtx stx other =
  throwError $ WrongMacroContext stx PatternCaseCtx (problemContext other)


expandOneForm :: MacroDest -> Syntax -> Expand ()
expandOneForm prob stx
  | Just ident <- identifierHeaded stx = do
      b <- resolve =<< addRootScope ident
      v <- getEValue b
      case v of
        EPrimExprMacro impl -> do
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
                  varInfo <- traverse Prims.prepareVar patVars
                  modifyState $
                    set (expanderPatternBinders . at (Left dest)) $
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
          (dest, outScopesDest) <- requireDeclarationCtx stx prob
          impl dest outScopesDest stx
        EPrimTypeMacro implT implP ->
          case prob of
            TypeDest dest ->
              implT dest stx
            TypePatternDest _exprTy dest ->
              implP dest stx
            otherDest ->
              throwError $ WrongMacroContext stx TypeCtx (problemContext otherDest)
        EPrimPatternMacro impl -> do
          dest <- requirePatternCtx stx prob
          impl dest stx
        EPrimUniversalMacro impl ->
          impl prob stx
        EVarMacro var -> do
          (t, dest) <- requireExpressionCtx stx prob
          case syntaxE stx of
            Id _ ->
              forkExpandVar t dest stx var
            String _ -> error "Impossible - string not ident"
            Sig _ -> error "Impossible - signal not ident"
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
                  res <- interpretMacroAction prob act
                  case res of
                    StuckOnSignal sig kont ->
                      forkAwaitingSignal prob sig kont
                    StuckOnType loc ty env cases kont ->
                      forkAwaitingTypeCase loc prob ty env cases kont
                    Done expanded ->
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
      DeclTreeDest {} ->
        throwError $ InternalError "All declarations should be identifier-headed"
      TypeDest {} ->
        throwError $ NotValidType stx
      PatternDest {} ->
        throwError $ InternalError "All patterns should be identifier-headed"
      TypePatternDest {} ->
        throwError $ InternalError "All type patterns should be identifier-headed"
      ExprDest t dest ->
        case syntaxE stx of
          List xs -> expandOneExpression t dest (addApp List stx xs)
          Sig s -> do
            unify dest (Ty TSignal) t
            expandLiteralSignal dest s
            saveExprType dest t
          String s -> expandLiteralString dest s
          Id _ -> error "Impossible happened - identifiers are identifier-headed!"


-- | Each declaration form fills a node in the declaration tree, and also fills
-- a DeclOutputScopesPtr with the scopes it introduces, so that later code can
-- see the newly-bound names.
expandDeclForm :: DeclTreePtr -> DeclOutputScopesPtr -> Syntax -> Expand ()
expandDeclForm dest outScopesDest stx =
  expandOneForm (DeclTreeDest dest outScopesDest) stx

-- | Like a single declaration form, a declaration group both fills a node in
-- the declaration tree and fills a DeclOutputScopesPtr with the scopes it
-- introduces. However, since expandDeclForms is recursive, some of those
-- scopes (those in the given ScopeSet) have already been introduced before
-- this call. We must merge those with the scopes which will be introduced by
-- the declarations in the rest of the Syntax.
expandDeclForms :: DeclTreePtr -> ScopeSet -> DeclOutputScopesPtr -> Syntax -> Expand ()
expandDeclForms dest scs outScopesDest (Syntax (Stx _ _ (List []))) = do
  linkDeclTree dest DeclTreeLeaf
  linkDeclOutputScopes outScopesDest scs
expandDeclForms dest scs outScopesDest (Syntax (Stx stxScs loc (List (d:ds)))) = do
  headDest <- newDeclTreePtr
  tailDest <- newDeclTreePtr
  headValidityPtr <- newDeclOutputScopesPtr
  linkDeclTree dest (DeclTreeBranch headDest tailDest)

  -- The head declaration will fill the headValidityPtr with the scopes it
  -- introduces, and then the ExpandDeclForms task will fill outScopesDest with
  -- the combination of scs, headValidityPtr's scopes, and the scopes introduced
  -- by the tail's declarations.
  expandDeclForm headDest headValidityPtr =<< addRootScope d
  forkExpanderTask $ ExpandDeclForms tailDest scs headValidityPtr outScopesDest (Syntax (Stx stxScs loc (List ds)))
expandDeclForms _dest _scs _outScopesDest _stx =
  error "TODO real error message - malformed module body"


-- | Link the destination to a literal signal object
expandLiteralSignal :: SplitCorePtr -> Signal -> Expand ()
expandLiteralSignal dest signal = linkExpr dest (CoreSignal signal)

expandLiteralString :: SplitCorePtr -> Text -> Expand ()
expandLiteralString _dest str =
  throwError $ InternalError $ "Strings are not valid expressions yet: " ++ show str

data MacroOutput
  = StuckOnSignal Signal [Closure]
  | StuckOnType SrcLoc Ty VEnv [(TypePattern, Core)] [Closure]
  | Done Value

-- If we're stuck waiting on a signal, we return that signal and a continuation
-- in the form of a sequence of closures. The first closure should be applied to
-- the result of wait-signal, the second to the result of the first, etc.
interpretMacroAction :: MacroDest -> MacroAction -> Expand MacroOutput
interpretMacroAction prob =
  \case
    MacroActionPure value-> do
      pure $ Done value
    MacroActionBind macroAction closure ->
      interpretMacroAction prob macroAction >>=
      \case
        StuckOnSignal signal closures ->
          pure $ StuckOnSignal signal (closures ++ [closure])
        StuckOnType loc ty env cases closures ->
          pure $ StuckOnType loc ty env cases (closures ++ [closure])
        Done boundResult -> do
          phase <- view (expanderLocal . expanderPhase)
          s <- getState
          let env = fromMaybe Env.empty .
                    view (expanderWorld . worldEnvironments . at phase) $
                    s
          value <- expandEval $ withEnv env $ apply closure boundResult
          case value of
            ValueMacroAction act -> interpretMacroAction prob act
            other -> throwError $ ValueNotMacro other
    MacroActionSyntaxError syntaxError ->
      throwError $ MacroRaisedSyntaxError syntaxError
    MacroActionSendSignal signal -> do
      setIORef expanderState (expanderReceivedSignals . at signal) (Just ())
      pure $ Done $ primitiveCtor "unit" []
    MacroActionWaitSignal signal ->
      pure $ StuckOnSignal signal []
    MacroActionIdentEq how v1 v2 -> do
      id1 <- getIdent v1
      id2 <- getIdent v2
      case how of
        Free ->
          compareFree id1 id2
            `catchError`
            \case
              -- Ambiguous bindings should not crash the comparison -
              -- they're just not free-identifier=?.
              Ambiguous _ _ _ -> return $ Done $ primitiveCtor "false" []
              -- Similarly, things that are not yet bound are just not
              -- free-identifier=?
              Unknown _ -> return $ Done $ primitiveCtor "false" []
              e -> throwError e
        Bound ->
          return $ Done $ flip primitiveCtor [] $
            if view stxValue id1 == view stxValue id2 &&
               view stxScopeSet id1 == view stxScopeSet id2
              then "true" else "false"
      where
        getIdent (ValueSyntax stx) = mustBeIdent stx
        getIdent _other = throwError $ InternalError $ "Not a syntax object in " ++ opName
        compareFree id1 id2 = do
          b1 <- resolve id1
          b2 <- resolve id2
          return $ Done $
            flip primitiveCtor [] $
            if b1 == b2 then "true" else "false"
        opName =
          case how of
            Free  -> "free-identifier=?"
            Bound -> "bound-identifier=?"
    MacroActionLog stx -> do
      liftIO $ prettyPrint stx >> putStrLn ""
      pure $ Done $ primitiveCtor "unit" []
    MacroActionIntroducer -> do
      sc <- freshScope "User introduction scope"
      pure $ Done $
        ValueClosure $ HO \(ValueCtor ctor []) -> ValueClosure $ HO \(ValueSyntax stx) ->
        ValueSyntax
          case view (constructorName . constructorNameText) ctor of
            "add" -> addScope' stx sc
            "flip" -> flipScope' stx sc
            "remove" -> removeScope' stx sc
            _ -> error "Impossible!"
    MacroActionWhichProblem -> do
      case prob of
        ExprDest t _stx -> pure $ Done $ primitiveCtor "expression" [ValueType t]
        TypeDest {} -> pure $ Done $ primitiveCtor "type" []
        DeclTreeDest {} -> pure $ Done $ primitiveCtor "declaration" []
        PatternDest {} -> pure $ Done $ primitiveCtor "pattern" []
        TypePatternDest {} -> pure $ Done $ primitiveCtor "type-pattern" []
    MacroActionTypeCase env loc ty cases -> do
      pure $ StuckOnType loc ty env cases []
