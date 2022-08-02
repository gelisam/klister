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
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Traversable
import System.Directory
import System.IO (Handle)

import Binding
import Core
import Datatype
import qualified Env
import Evaluator
import qualified Expander.Primitives as Prims
import Expander.DeclScope
import Expander.Syntax
import Expander.Monad
import Expander.TC
import Kind
import Module
import ModuleName
import Parser
import Phase
import Pretty
import ScopeSet (ScopeSet)
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
  t <- tMetaVar <$> freshMeta (Just KStar)
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
  importing modName $
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
    let m'' = over ScopeSet.allScopeSets (ScopeSet.insertUniversally sc) m'
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
  p <- currentPhase
  dts <- view expanderKernelDatatypes <$> getState
  modifyState $
    over (expanderWorld . worldDatatypes . at p . non Map.empty) $
    Map.union dts
  ctors <- view expanderKernelConstructors <$> getState
  modifyState $
    over (expanderWorld . worldConstructors . at p . non Map.empty) $
    Map.union ctors
  vals <- view expanderKernelValues <$> getState
  modifyState $
    over (expanderWorld . worldEnvironments . at p) $
    \case
      Nothing -> Just (snd <$> vals)
      Just env -> Just (env <> (snd <$> vals))
  modifyState $
    over (expanderWorld . worldTypeContexts . at p . non mempty) $ (<> (fst <$> vals))
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
        Data _ dn argKinds ctors -> do
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
            Map.insert dt $ DatatypeInfo
              { _datatypeArgKinds     = argKinds
              , _datatypeConstructors = [c | (_, c, _) <- ctors ]
              }

        Example loc sch expr -> do
          env <- lift currentEnv
          value <- lift $ expandEval (eval expr)
          tell $ [ExampleResult loc env expr sch value]
        Run loc expr -> do
          lift (expandEval (eval expr)) >>=
            \case
              (ValueIOAction act) ->
                tell $ [IOResult $ void $ act]
              _ -> throwError $ InternalError $
                   "While running an action at " ++
                   T.unpack (pretty loc) ++
                   " an unexpected non-IO value was encountered."
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


initializeKernel :: Handle -> Expand ()
initializeKernel outputChannel = do
  traverse_ (uncurry addExprPrimitive) exprPrims
  traverse_ (uncurry addModulePrimitive) modPrims
  traverse_ (uncurry addDeclPrimitive) declPrims
  traverse_ (uncurry addTypePrimitive) typePrims
  traverse_ (uncurry addPatternPrimitive) patternPrims
  traverse_ addDatatypePrimitive datatypePrims
  traverse_ addFunPrimitive funPrims
  addUniversalPrimitive "with-unknown-type" Prims.makeLocalType


  where
    typePrims :: [(Text, (Kind -> SplitTypePtr -> Syntax -> Expand (), TypePatternPtr -> Syntax -> Expand ()))]
    typePrims =
      [ ("Syntax", Prims.baseType tSyntax)
      , ("String", Prims.baseType tString)
      , ("Integer", Prims.baseType tInteger)
      , ("->", Prims.arrowType)
      , ("Macro", Prims.macroType)
      , ("IO", Prims.ioType)
      , ("Output-Port", Prims.baseType tOutputPort)
      , ("Type", Prims.baseType tType)
      ]

    funPrims :: [(Text, Scheme Ty, Value)]
    funPrims =
      [ ( "open-syntax"
        , Scheme [] $ tFun [tSyntax] (Prims.primitiveDatatype "Syntax-Contents" [tSyntax])
        , ValueClosure $ HO $
          \(ValueSyntax stx) ->
            case syntaxE stx of
              Id name ->
                primitiveCtor "identifier-contents" [ValueString name]
              String str ->
                primitiveCtor "string-contents" [ValueString str]
              LitInt i ->
                primitiveCtor "integer-contents" [ValueInteger i]
              List xs ->
                primitiveCtor "list-contents" [foldr consVal nilVal xs]
                where
                  nilVal = primitiveCtor "nil" []
                  consVal x v = primitiveCtor "::" [ValueSyntax x, v]
        )
      , ( "close-syntax"
        , Scheme [] $
          tFun [tSyntax, tSyntax, Prims.primitiveDatatype "Syntax-Contents" [tSyntax]] tSyntax
        , ValueClosure $ HO $
          \(ValueSyntax locStx) ->
            ValueClosure $ HO $
            \(ValueSyntax scopesStx) ->
              ValueClosure $ HO $
              -- N.B. Assuming correct constructors
              \(ValueCtor ctor [arg]) ->
                let close x = Syntax $ Stx (view (unSyntax . stxScopeSet) scopesStx) (stxLoc locStx) x
                    unList =
                      \case
                        (ValueCtor c [])
                          | view (constructorName . constructorNameText) c == "nil" ->
                            []
                        (ValueCtor c [ValueSyntax x, xs])
                          | view (constructorName . constructorNameText) c == "::" -> x : unList xs
                        _ ->
                          error "impossible: List value must be nil or ::"
                in
                  ValueSyntax $
                  case (view (constructorName . constructorNameText) ctor, arg) of
                    ("identifier-contents", ValueString name) ->
                      close (Id name)
                    ("string-contents", ValueString str) ->
                      close (String str)
                    ("integer-contents", ValueInteger i) ->
                      close (LitInt i)
                    ("list-contents", unList -> lst) ->
                      close (List lst)
                    _ ->
                      error "impossible: Syntax-Contents value must be one of its constructors"
        )
      ] ++
      [ ( "string=?"
        , Scheme [] $ tFun [tString, tString] (Prims.primitiveDatatype "Bool" [])
        , ValueClosure $ HO $
          \(ValueString str1) ->
            ValueClosure $ HO $
            \(ValueString str2) ->
              if str1 == str2
                then primitiveCtor "true" []
                else primitiveCtor "false" []
        )
      , ( "string-append"
        , Scheme [] $ tFun [tString, tString] tString
        , ValueClosure $ HO $
          \(ValueString str1) ->
            ValueClosure $ HO $
            \(ValueString str2) ->
              ValueString (str1 <> str2)
        )
      , ( "integer->string"
        , Scheme [] $ tFun [tInteger] tString
        , ValueClosure $ HO $
          \(ValueInteger int) ->
            ValueString (T.pack (show int))
        )
      , ( "substring"
        , Scheme [] $
          tFun [tInteger, tInteger, tString] (Prims.primitiveDatatype "Maybe" [tString])
        , ValueClosure $ HO $
          \(ValueInteger (fromInteger -> start)) ->
            ValueClosure $ HO $
            \(ValueInteger (fromInteger -> len)) ->
              ValueClosure $ HO $
              \(ValueString str) ->
                if | start < 0 || start       >= T.length str -> primitiveCtor "nothing" []
                   | len   < 0 || start + len >  T.length str -> primitiveCtor "nothing" []
                   | otherwise ->
                     primitiveCtor "just" [ValueString $ T.take len $ T.drop start str]
        )
      , ( "string-length"
        , Scheme [] $ tFun [tString] tInteger
        , ValueClosure $ HO $ \(ValueString str) -> ValueInteger $ toInteger $ T.length str
        )
      , ( "string-downcase"
        , Scheme [] $ tFun [tString] tString
        , ValueClosure $ HO $ \(ValueString str) -> ValueString $ T.toLower str
        )
      , ( "string-upcase"
        , Scheme [] $ tFun [tString] tString
        , ValueClosure $ HO $ \(ValueString str) -> ValueString $ T.toUpper str
        )
      , ( "string-titlecase"
        , Scheme [] $ tFun [tString] tString
        , ValueClosure $ HO $ \(ValueString str) -> ValueString $ T.toTitle str
        )
      , ( "string-foldcase"
        , Scheme [] $ tFun [tString] tString
        , ValueClosure $ HO $ \(ValueString str) -> ValueString $ T.toCaseFold str
        )
      ] ++
      [ ( "string" <> name <> "?"
        , Scheme [] $ tFun [tString, tString] (Prims.primitiveDatatype "Bool" [])
        , Prims.binaryStringPred fun
        )
      | (name, fun) <- [("<", (<)), ("<=", (<=)), (">", (>)), (">=", (>=)), ("=", (==)), ("/=", (/=))]
      ] ++
      [
        ( name
        , Scheme [] $ tFun [tInteger] tInteger
        , Prims.unaryIntPrim fun
        )
      | (name, fun) <- [("abs", abs), ("negate", negate)]
      ] ++
      [ ( name
        , Scheme [] $ tFun [tInteger, tInteger] tInteger
        , Prims.binaryIntPrim fun
        )
      | (name, fun) <- [("+", (+)), ("-", (-)), ("*", (*)), ("/", div)]
      ] ++
      [ ( name
        , Scheme [] $ tFun [tInteger, tInteger] (Prims.primitiveDatatype "Bool" [])
        , Prims.binaryIntPred fun
        )
      | (name, fun) <- [("<", (<)), ("<=", (<=)), (">", (>)), (">=", (>=)), ("=", (==)), ("/=", (/=))]
      ] ++
      [ ("pure-IO"
        , Scheme [KStar, KStar] $ tFun [tSchemaVar 0 []] (tIO (tSchemaVar 0 []))
        , ValueClosure $ HO $ \v -> ValueIOAction (pure v)
        )
      , ("bind-IO"
        , Scheme [KStar, KStar] $
          tFun [ tIO (tSchemaVar 0 [])
               , tFun [tSchemaVar 0 []] (tIO (tSchemaVar 1 []))
               ]
               (tIO (tSchemaVar 1 []))
        , ValueClosure $ HO $ \(ValueIOAction m) ->
            ValueClosure $ HO $ \(ValueClosure f) ->
            ValueIOAction $ do
            v <- m
            case f of
              HO fun -> do
                let ValueIOAction io = fun v
                io
              FO clos -> do
                let env = view closureEnv clos
                    var = view closureVar clos
                    ident = view closureIdent clos
                    body = view closureBody clos
                out <- runExceptT $ flip runReaderT env $ runEval $
                  withExtendedEnv ident var v $
                  eval body
                case out of
                  Left err -> error (T.unpack (pretty err))
                  Right done -> pure done
        )
      , ( "stdout"
        , Scheme [] $ tOutputPort
        , ValueOutputPort outputChannel
        )
      , ( "write"
        , Scheme [] $ tFun [tOutputPort, tString] (tIO (Prims.primitiveDatatype "Unit" []))
        , ValueClosure $ HO $
          \(ValueOutputPort h) ->
            ValueClosure $ HO $
            \(ValueString str) ->
              ValueIOAction $ do
                T.hPutStr h str
                pure (primitiveCtor "unit" [])
        )
      ]

    datatypePrims :: [(Text, [Kind], [(Text, [Ty])])]
    datatypePrims =
      [ ("ScopeAction", [], [("flip", []), ("add", []), ("remove", [])])
      , ("Unit", [], [("unit", [])])
      , ("Bool", [], [("true", []), ("false", [])])
      , ("Problem", [], [("declaration", []), ("type", []), ("expression", [tType]), ("pattern", []), ("type-pattern", [])])
      , ("Maybe", [KStar], [("nothing", []), ("just", [tSchemaVar 0 []])])
      , ("List"
        , [KStar]
        , [ ("nil", [])
          , ("::", [tSchemaVar 0 [], Prims.primitiveDatatype "List" [tSchemaVar 0 []]])
          ]
        )
      , ("Syntax-Contents"
        , [KStar]
        , [ ("list-contents", [Prims.primitiveDatatype "List" [tSchemaVar 0 []]])
          , ("integer-contents", [tInteger])
          , ("string-contents", [tString])
          , ("identifier-contents", [tString])
          -- if you add a constructor here, remember to also add a
          -- corresponding pattern in close-syntax!
          ]
        )
      ]

    modPrims :: [(Text, Syntax -> Expand ())]
    modPrims = [("#%module", Prims.makeModule expandDeclForms)]

    declPrims :: [(Text, DeclTreePtr -> DeclOutputScopesPtr -> Syntax -> Expand ())]
    declPrims =
      [ ("define", Prims.define)
      , ("datatype", Prims.datatype)
      , ("define-macros", Prims.defineMacros)
      , ("example", Prims.example)
      , ("run", Prims.run)
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
      , ("bound-identifier=?", Prims.identEqual Bound)
      , ("free-identifier=?", Prims.identEqual Free)
      , ("quote", Prims.quote)
      , ("ident", Prims.ident)
      , ("ident-syntax", Prims.identSyntax)
      , ("empty-list-syntax", Prims.emptyListSyntax)
      , ("cons-list-syntax", Prims.consListSyntax)
      , ("list-syntax", Prims.listSyntax)
      , ("string-syntax", Prims.stringSyntax)
      , ("replace-loc", Prims.replaceLoc)
      , ("syntax-case", Prims.syntaxCase)
      , ("let-syntax", Prims.letSyntax)
      , ("log", Prims.log)
      , ("make-introducer", Prims.makeIntroducer)
      , ("which-problem", Prims.whichProblem)
      , ("case", Prims.dataCase)
      , ("type-case", Prims.typeCase)
      ]

    patternPrims :: [(Text, Either (Ty, PatternPtr) TypePatternPtr -> Syntax -> Expand ())]
    patternPrims = [("else", Prims.elsePattern)]

    addToKernel name p b =
      modifyState $ over expanderKernelExports $ addExport p name b

    addFunPrimitive :: (Text, Scheme Ty, Value) -> Expand ()
    addFunPrimitive (name, sch, val) = do
      x <- freshVar
      ptr <- liftIO newSchemePtr
      linkScheme ptr sch

      modifyState $ set (expanderKernelValues . at x) $ Just $ (Stx mempty kernelLoc name, (ptr, val))
      b <- freshBinding
      bind b $ EVarMacro x
      addToKernel name runtime b

      where
        kernelLoc = SrcLoc "<kernel>" (SrcPos 0 0) (SrcPos 0 0)

    addDatatypePrimitive :: (Text, [Kind], [(Text, [Ty])]) -> Expand ()
    addDatatypePrimitive (name, argKinds, ctors) = do
      let dn = DatatypeName name
      let dt = Datatype
                 { _datatypeModule = KernelName kernelName
                 , _datatypeName = dn
                 }
      let tyImpl =
             \k dest stx -> do
               equateKinds stx KStar k
               Stx _ _ (me, args) <- mustBeCons stx
               _ <- mustBeIdent me
               if length args /= length argKinds
                 then throwError $ WrongDatatypeArity stx dt
                                     (fromIntegral $ length argKinds)
                                     (length args)
                 else do
                   argDests <- traverse (uncurry scheduleType) (zip argKinds args)
                   linkType dest $ tDatatype dt argDests
          patImpl =
            \dest stx -> do
              Stx _ _ (me, args) <- mustBeCons stx
              _ <- mustBeIdent me
              if length args /= length argKinds
                then throwError $ WrongDatatypeArity stx dt
                                    (fromIntegral $ length argKinds)
                                    (length args)
                else do
                  varInfo <- traverse Prims.prepareVar args
                  sch <- trivialScheme tType
                  linkTypePattern dest
                    (TypePattern $ tDatatype dt [(varStx, var) | (_, varStx, var) <- varInfo])
                    [ (sc, n, x, sch)
                    | (sc, n, x) <- varInfo
                    ]
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
            { _datatypeArgKinds = argKinds
            , _datatypeConstructors = ctors'
            }
      modifyState $
        over expanderKernelDatatypes $
        Map.insert dt info


    addPatternPrimitive ::
      Text -> (Either (Ty, PatternPtr) TypePatternPtr -> Syntax -> Expand ()) -> Expand ()
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
      (Kind -> SplitTypePtr -> Syntax -> Expand (), TypePatternPtr -> Syntax -> Expand ()) ->
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
      | [Syntax (Stx _ _ (Id "shift")), spec, Syntax (Stx _ _ (LitInt i))] <- elts = do
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
                (Syntax (Stx _ _ (LitInt i)) : more) -> do
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
        ModuleDest ->
          expandModuleForm stx
        DeclTreeDest d outScopesDest ->
          expandDeclForm d outScopesDest stx
        TypeDest k d ->
          expandOneType k d stx
        ExprDest t d ->
          expandOneExpression t d stx
        PatternDest scrutT d ->
          expandOnePattern scrutT d stx
        TypePatternDest d ->
          expandOneTypePattern d stx
    AwaitingType tdest after ->
      linkedType tdest >>=
      \case
        Nothing -> stillStuck tid task
        Just ty ->
          for_ after $
          \case
            TypeThenUnify dest ty' ->
              unify dest ty' ty
            TypeThenExpandExpr dest stx ->
              forkExpandSyntax (ExprDest ty dest) stx
    AwaitingTypeCase loc dest ty env cases kont -> do
      Ty t <- normType ty
      case t of
        TyF (TMetaVar ptr') _ -> do
          -- Always wait on the canonical representative
          case ty of
            Ty (TyF (TMetaVar ptr) _) | ptr == ptr' -> stillStuck tid task
            _ -> forkAwaitingTypeCase loc dest (tMetaVar ptr') env cases kont
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
          specialize eDest sch >>= unify eDest ty
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
      ready <- do
        let patternComplete ptr =
              (view (expanderCompletedPatterns . at ptr) <$> getState) >>=
              \case
                Nothing ->
                  pure False
                Just layer ->
                  and <$> traverse patternComplete layer
        patternComplete patPtr
      if not ready
        then stillStuck tid task
        else do
          let getVarInfo ptr =
                (view (expanderPatternBinders . at ptr) <$> getState) >>=
                \case
                  Nothing ->
                    throwError $ InternalError "Pattern info not added"
                  Just (Right found) ->
                    pure [found]
                  Just (Left ptrs) ->
                    concat <$> traverse getVarInfo ptrs
          vars <- getVarInfo patPtr
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
    AwaitingTypePattern patPtr ty dest stx -> do
      ready <- has (expanderCompletedTypePatterns . ix patPtr) <$> getState
      if not ready
        then stillStuck tid task
        else do
          varInfo <- view (expanderTypePatternBinders . at patPtr) <$> getState
          case varInfo of
            Nothing -> throwError $ InternalError "Type pattern info not added"
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


expandOneType :: Kind -> SplitTypePtr -> Syntax -> Expand ()
expandOneType k dest stx = expandOneForm (TypeDest k dest) stx

expandOneExpression :: Ty -> SplitCorePtr -> Syntax -> Expand ()
expandOneExpression t dest stx = expandOneForm (ExprDest t dest) stx

expandOnePattern :: Ty -> PatternPtr -> Syntax -> Expand ()
-- This case means that identifier-only macro invocations aren't valid in pattern contexts
expandOnePattern scrutTy dest var@(Syntax (Stx _ _ (Id _))) = do
  ty <- trivialScheme scrutTy
  (sc, x, v) <- Prims.prepareVar var
  modifyState $ set (expanderPatternBinders . at dest) $ Just $ Right (sc, x, v, ty)
  linkPattern dest $ PatternVar x v
expandOnePattern scrutTy dest stx =
  expandOneForm (PatternDest scrutTy dest) stx

expandOneTypePattern :: TypePatternPtr -> Syntax -> Expand ()
expandOneTypePattern dest stx =
  expandOneForm (TypePatternDest dest) stx



-- | Insert a function application marker with a lexical context from
-- the original expression
addApp :: (forall a . [a] -> ExprF a) -> Syntax -> [Syntax] -> Syntax
addApp ctor (Syntax (Stx scs loc _)) args =
  Syntax (Stx scs loc (ctor (app : args)))
  where
    app = Syntax (Stx scs loc (Id "#%app"))

problemCategory :: MacroDest -> SyntacticCategory
problemCategory (ModuleDest {}) = ModuleCat
problemCategory (DeclTreeDest {}) = DeclarationCat
problemCategory (TypeDest {}) = TypeCat
problemCategory (ExprDest {}) = ExpressionCat
problemCategory (PatternDest {}) = PatternCaseCat
problemCategory (TypePatternDest {}) = TypePatternCaseCat

requireDeclarationCat :: Syntax -> MacroDest -> Expand (DeclTreePtr, DeclOutputScopesPtr)
requireDeclarationCat _ (DeclTreeDest dest outScopesDest) = return (dest, outScopesDest)
requireDeclarationCat stx other =
  throwError $ WrongSyntacticCategory stx DeclarationCat (problemCategory other)

requireTypeCat :: Syntax -> MacroDest -> Expand (Kind, SplitTypePtr)
requireTypeCat _ (TypeDest kind dest) = return (kind, dest)
requireTypeCat stx other =
  throwError $ WrongSyntacticCategory stx TypeCat (problemCategory other)

requireExpressionCat :: Syntax -> MacroDest -> Expand (Ty, SplitCorePtr)
requireExpressionCat _ (ExprDest ty dest) = return (ty, dest)
requireExpressionCat stx other =
  throwError $ WrongSyntacticCategory stx ExpressionCat (problemCategory other)

requirePatternCat :: Syntax -> MacroDest -> Expand (Either (Ty, PatternPtr) TypePatternPtr)
requirePatternCat _ (PatternDest scrutTy dest) =
  return $ Left (scrutTy, dest)
requirePatternCat _ (TypePatternDest dest) =
  return $ Right dest
requirePatternCat stx other =
  throwError $ WrongSyntacticCategory stx PatternCaseCat (problemCategory other)


expandOneForm :: MacroDest -> Syntax -> Expand ()
expandOneForm prob stx
  | Just ident <- identifierHeaded stx = do
      b <- resolve =<< addRootScope ident
      v <- getEValue b
      case v of
        EPrimExprMacro impl -> do
          (t, dest) <- requireExpressionCat stx prob
          saveExprType dest t
          impl t dest stx
        EConstructor ctor -> do
          ConstructorInfo args dt <- constructorInfo ctor
          DatatypeInfo argKinds _ <- datatypeInfo dt
          case prob of
            ExprDest t dest -> do
              argTys <- traverse makeTypeMeta argKinds
              unify dest t $ tDatatype dt argTys
              args' <- for args \a -> inst dest (Scheme argKinds a) argTys
              Stx _ _ (foundName, foundArgs) <- mustBeCons stx
              _ <- mustBeIdent foundName
              argDests <-
                if length foundArgs /= length args'
                  then throwError $
                       WrongArgCount stx ctor (length args') (length foundArgs)
                  else for (zip args' foundArgs) (uncurry schedule)
              linkExpr dest (CoreCtor ctor argDests)
              saveExprType dest t
            PatternDest patTy dest -> do
              Stx _ loc (_cname, subPats) <- mustBeCons stx
              tyArgs <- traverse makeTypeMeta argKinds
              argTypes <- for args \ a ->
                            inst loc (Scheme argKinds a) tyArgs
              unify loc (tDatatype dt tyArgs) patTy
              if length subPats /= length argTypes
                then throwError $ WrongArgCount stx ctor (length argTypes) (length subPats)
                else do
                  subPtrs <- for (zip subPats argTypes) \(sp, t) -> do
                    ptr <- liftIO newPatternPtr
                    let subPatDest = PatternDest t ptr
                    forkExpandSyntax subPatDest sp
                    pure ptr
                  modifyState $ set (expanderPatternBinders . at dest) $ Just $ Left subPtrs
                  linkPattern dest $
                    CtorPattern ctor subPtrs
            other ->
              throwError $ WrongSyntacticCategory stx ExpressionCat (problemCategory other)
        EPrimModuleMacro impl ->
          case prob of
            ModuleDest -> do
              impl stx
            other ->
              throwError $ WrongSyntacticCategory stx ModuleCat (problemCategory other)
        EPrimDeclMacro impl -> do
          (dest, outScopesDest) <- requireDeclarationCat stx prob
          impl dest outScopesDest stx
        EPrimTypeMacro implT implP ->
          case prob of
            TypeDest k dest ->
              implT k dest stx
            TypePatternDest dest ->
              implP dest stx
            otherDest ->
              throwError $ WrongSyntacticCategory stx TypeCat (problemCategory otherDest)
        EPrimPatternMacro impl -> do
          dest <- requirePatternCat stx prob
          impl dest stx
        EPrimUniversalMacro impl ->
          impl prob stx
        EVarMacro var -> do
          (t, dest) <- requireExpressionCat stx prob
          case syntaxE stx of
            Id _ ->
              forkExpandVar t dest stx var
            String _ -> error "Impossible - string not ident"
            LitInt _ -> error "Impossible - literal integer not ident"
            List xs -> expandOneExpression t dest (addApp List stx xs)
        ETypeVar k i -> do
          (k', dest) <- requireTypeCat stx prob
          case syntaxE stx of
            List (vStx@(syntaxE -> Id _) : arg : args) -> do
              kindedArgs <- for (arg : args) $
                            \a -> do
                              newKind <- KMetaVar <$> liftIO newKindVar
                              pure (newKind, a)
              equateKinds vStx k $ kFun (map fst kindedArgs) k'
              argDests <- traverse (uncurry scheduleType) kindedArgs
              linkType dest $ tSchemaVar i argDests
            Id _ -> do
              equateKinds stx k k'
              linkType dest $ tSchemaVar i []
            _ -> throwError $ NotValidType stx

        EIncompleteDefn x n d -> do
          (t, dest) <- requireExpressionCat stx prob
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
      ModuleDest {} ->
        throwError $ InternalError "All modules should be identifier-headed"
      DeclTreeDest {} ->
        throwError $ InternalError "All declarations should be identifier-headed"
      TypeDest {} ->
        throwError $ NotValidType stx
      ExprDest t dest ->
        case syntaxE stx of
          List xs -> expandOneExpression t dest (addApp List stx xs)
          LitInt s -> do
            unify dest t tInteger
            expandLiteralInteger dest s
            saveExprType dest t
          String s -> do
            unify dest t tString
            expandLiteralString dest s
            saveExprType dest t
          Id _ -> error "Impossible happened - identifiers are identifier-headed!"
      PatternDest {} ->
        throwError $ InternalError "All patterns should be identifier-headed"
      TypePatternDest {} ->
        throwError $ InternalError "All type patterns should be identifier-headed"


expandModuleForm :: Syntax -> Expand ()
expandModuleForm stx = do
  expandOneForm ModuleDest stx

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


-- | Link the destination to a literal integer object
expandLiteralInteger :: SplitCorePtr -> Integer -> Expand ()
expandLiteralInteger dest i = linkExpr dest (CoreInteger i)

expandLiteralString :: SplitCorePtr -> Text -> Expand ()
expandLiteralString dest str = do
  linkExpr dest (CoreString str)

data MacroOutput
  = StuckOnType SrcLoc Ty VEnv [(TypePattern, Core)] [Closure]
  | Done Value

-- If we're stuck waiting on type information, we return a continuation in the
-- form of a sequence of closures. The first closure should be applied to the
-- resulting information, the second to the result of the first, etc.
interpretMacroAction :: MacroDest -> MacroAction -> Expand MacroOutput
interpretMacroAction prob =
  \case
    MacroActionPure value-> do
      pure $ Done value
    MacroActionBind macroAction closure ->
      interpretMacroAction prob macroAction >>=
      \case
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
        ModuleDest {} -> pure $ Done $ primitiveCtor "module" []
        DeclTreeDest {} -> pure $ Done $ primitiveCtor "declaration" []
        TypeDest {} -> pure $ Done $ primitiveCtor "type" []
        ExprDest t _stx -> pure $ Done $ primitiveCtor "expression" [ValueType t]
        PatternDest {} -> pure $ Done $ primitiveCtor "pattern" []
        TypePatternDest {} -> pure $ Done $ primitiveCtor "type-pattern" []
    MacroActionTypeCase env loc ty cases -> do
      pure $ StuckOnType loc ty env cases []
