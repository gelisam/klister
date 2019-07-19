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
  -- * Expander monad
  , execExpand
  , expansionErrText
  , mkInitContext
  , initializeExpansionEnv
  , ExpansionErr(..)
  , ExpanderContext
  ) where

import Control.Lens hiding (List, children)
import Control.Monad.Except
import Control.Monad.Reader

import Data.Unique
import Data.List.Extra (maximumOn)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Traversable

import Core
import Env
import Evaluator
import Expander.Monad
import Module
import PartialCore
import Phase
import Scope
import ScopeSet (ScopeSet)
import Signals
import SplitCore
import Syntax
import Value
import qualified ScopeSet

expandExpr :: Syntax -> Expand SplitCore
expandExpr stx = do
  dest <- liftIO $ newSplitCorePtr
  addReady dest stx
  expandTasks
  children <- view expanderCompletedCore <$> getState
  return $ SplitCore { _splitCoreRoot = dest
                     , _splitCoreDescendants = children
                     }

expandModule :: ParsedModule Syntax -> Expand CompleteModule
expandModule src = do
  Stx _ _ lang <- mustBeIdent (view moduleLanguage src)
  if lang /= "kernel"
    then throwError $ InternalError $ T.unpack $
         "Custom languages not supported yet: " <> lang
    else pure () -- TODO load language bindings
  modBodyDest <- liftIO $ newModBodyPtr
  -- TODO error if module top is already set to something
  modifyState $ set expanderModuleTop $ Just modBodyDest
  readyDecls modBodyDest (view moduleContents src)
  expandTasks
  body <- getBody modBodyDest
  return $ Module
    { _moduleName = ModuleName $ view moduleSource src
    , _moduleImports = [] -- TODO
    , _moduleBody = body
    , _moduleExports = [] -- TODO
    }
  where
    getBody :: ModBodyPtr -> Expand [Decl Core]
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

    flatten :: Decl SplitCorePtr -> Expand (Decl Core)
    flatten (Define x v e) =
      linkedCore e >>=
      \case
        Nothing -> throwError $ InternalError "Missing expr after expansion"
        Just e' -> pure $ Define x v e'
    flatten (DefineMacros macros) =
      DefineMacros <$>
      for macros \(x, e) ->
        linkedCore e >>=
        \case
          Nothing -> throwError $ InternalError "Missing expr after expansion"
          Just e' -> pure $ (x, e')
    flatten (Meta d) =
      Meta <$> flatten d
    flatten (Example e) =
      linkedCore e >>=
      \case
        Nothing -> throwError $ InternalError "Missing expr after expansion"
        Just e' -> pure $ Example e'


freshBinding :: Expand Binding
freshBinding = Binding <$> liftIO newUnique

getEValue :: Binding -> Expand EValue
getEValue b = do
  ExpansionEnv env <- view expanderExpansionEnv <$> getState
  case Map.lookup b env of
    Just v -> return v
    Nothing -> throwError (InternalError "No such binding")



link :: SplitCorePtr -> CoreF SplitCorePtr -> Expand ()
link dest layer =
  modifyState $
  \st -> st { _expanderCompletedCore =
              _expanderCompletedCore st <> Map.singleton dest layer
            }

linkDecl :: DeclPtr -> Decl SplitCorePtr -> Expand ()
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


getTasks :: Expand [(TaskID, ExpanderTask)]
getTasks = view expanderTasks <$> getState

clearTasks :: Expand ()
clearTasks = modifyState $ \st -> st { _expanderTasks = [] }


currentEnv :: Expand (Env Value)
currentEnv = do
  phase <- currentPhase
  maybe Env.empty id . view (expanderEnvironments . at phase) <$> getState


expandEval :: Eval a -> Expand a
expandEval evalAction = do
  env <- currentEnv
  out <- liftIO $ runExceptT $ runReaderT (runEval evalAction) env
  case out of
    Left err -> throwError $ MacroEvaluationError err
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
       then throwError (Ambiguous blame)
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

mustBeIdent :: Syntax -> Expand (Stx Text)
mustBeIdent (Syntax (Stx scs srcloc (Id x))) = return (Stx scs srcloc x)
mustBeIdent other = throwError (NotIdentifier other)

mustBeEmpty :: Syntax -> Expand (Stx ())
mustBeEmpty (Syntax (Stx scs srcloc (List []))) = return (Stx scs srcloc ())
mustBeEmpty other = throwError (NotEmpty other)

mustBeCons :: Syntax -> Expand (Stx (Syntax, [Syntax]))
mustBeCons (Syntax (Stx scs srcloc (List (x:xs)))) = return (Stx scs srcloc (x, xs))
mustBeCons other = throwError (NotCons other)

mustBeList :: Syntax -> Expand (Stx [Syntax])
mustBeList (Syntax (Stx scs srcloc (List xs))) = return (Stx scs srcloc xs)
mustBeList other = throwError (NotList other)


class MustBeVec a where
  mustBeVec :: Syntax -> Expand (Stx a)

instance MustBeVec () where
  mustBeVec (Syntax (Stx scs srcloc (Vec []))) = return (Stx scs srcloc ())
  mustBeVec other = throwError (NotRightLength 0 other)

instance MustBeVec Syntax where
  mustBeVec (Syntax (Stx scs srcloc (Vec [x]))) = return (Stx scs srcloc x)
  mustBeVec other = throwError (NotRightLength 1 other)

instance MustBeVec (Syntax, Syntax) where
  mustBeVec (Syntax (Stx scs srcloc (Vec [x, y]))) = return (Stx scs srcloc (x, y))
  mustBeVec other = throwError (NotRightLength 2 other)

instance (a ~ Syntax, b ~ Syntax, c ~ Syntax) => MustBeVec (a, b, c) where
  mustBeVec (Syntax (Stx scs srcloc (Vec [x, y, z]))) = return (Stx scs srcloc (x, y, z))
  mustBeVec other = throwError (NotRightLength 3 other)

instance MustBeVec (Syntax, Syntax, Syntax, Syntax) where
  mustBeVec (Syntax (Stx scs srcloc (Vec [w, x, y, z]))) = return (Stx scs srcloc (w, x, y, z))
  mustBeVec other = throwError (NotRightLength 4 other)

instance MustBeVec (Syntax, Syntax, Syntax, Syntax, Syntax) where
  mustBeVec (Syntax (Stx scs srcloc (Vec [v, w, x, y, z]))) =
    return (Stx scs srcloc (v, w, x, y, z))
  mustBeVec other = throwError (NotRightLength 5 other)

instance MustBeVec [Syntax] where
  mustBeVec (Syntax (Stx scs srcloc (Vec xs))) =
    return (Stx scs srcloc xs)
  mustBeVec other = throwError (NotVec other)


resolveImports :: Syntax -> Expand ()
resolveImports _ = pure () -- TODO

buildExports :: Syntax -> Expand ()
buildExports _ = pure ()

initializeExpansionEnv :: Expand ()
initializeExpansionEnv = do
  _ <- traverse (uncurry addExprPrimitive) exprPrims
  _ <- traverse (uncurry addModulePrimitive) modPrims
  _ <- traverse (uncurry addDeclPrimitive) declPrims
  pure ()

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

                readyDecls bodyPtr body

                buildExports exports
                pure ()
        )
      ]

    declPrims :: [(Text, DeclPtr -> Syntax -> Expand ())]
    declPrims =
      [ ("define"
        , \ dest stx -> do
            Stx _ _ (_, varStx, expr) <- mustBeVec stx
            x <- mustBeIdent varStx
            b <- freshBinding
            addBinding x b
            var <- freshVar
            bind b (EVarMacro var)
            exprDest <- liftIO $ newSplitCorePtr
            linkDecl dest (Define x var exprDest)
            addReady exprDest expr
        )
      ,("define-macros"
        , \ dest stx -> do
            Stx _ _ (_ :: Syntax, macroList) <- mustBeVec stx
            Stx _ _ macroDefs <- mustBeList macroList
            macros <- for macroDefs $ \def -> do
              Stx _ _ (mname, mdef) <- mustBeVec def
              theName <- mustBeIdent mname
              b <- freshBinding
              addBinding theName b
              macroDest <- schedule mdef
              bind b $ EIncompleteMacro macroDest
              return (theName, macroDest)
            linkDecl dest $ DefineMacros macros

        )
      , ("example"
        , \ dest stx -> do
            Stx _ _ (_ :: Syntax, expr) <- mustBeVec stx
            exprDest <- liftIO $ newSplitCorePtr
            linkDecl dest (Example exprDest)
            addReady exprDest expr
        )
      ]

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
            link dest $ CoreLam arg' coreArg bodyDest
        )
      , ( "#%app"
        , \ dest stx -> do
            Stx _ _ (_, fun, arg) <- mustBeVec stx
            funDest <- schedule fun
            argDest <- schedule arg
            link dest $ CoreApp funDest argDest
        )
      , ( "pure"
        , \ dest stx -> do
            Stx _ _ (_ :: Syntax, v) <- mustBeVec stx
            argDest <- schedule v
            link dest $ CorePure argDest
        )
      , ( ">>="
        , \ dest stx -> do
            Stx _ _ (_, act, cont) <- mustBeVec stx
            actDest <- schedule act
            contDest <- schedule cont
            link dest $ CoreBind actDest contDest
        )
      , ( "syntax-error"
        , \dest stx -> do
            Stx scs srcloc (_, args) <- mustBeCons stx
            Stx _ _ (msg, locs) <- mustBeCons $ Syntax $ Stx scs srcloc (List args)
            msgDest <- schedule msg
            locDests <- traverse schedule locs
            link dest $ CoreSyntaxError (SyntaxError locDests msgDest)
        )
      , ( "send-signal"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, sig) <- mustBeVec stx
            sigDest <- schedule sig
            link dest $ CoreSendSignal sigDest
        )
      , ( "bound-identifier=?"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, id1, id2) <- mustBeVec stx
            newE <- CoreIdentEq Bound <$> schedule id1 <*> schedule id2
            link dest newE
        )
      , ( "free-identifier=?"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, id1, id2) <- mustBeVec stx
            newE <- CoreIdentEq Free <$> schedule id1 <*> schedule id2
            link dest newE
        )
      , ( "quote"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, quoted) <- mustBeVec stx
            link dest $ CoreSyntax quoted
        )
      , ( "if"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, b, t, f) <- mustBeVec stx
            link dest =<< CoreIf <$> schedule b <*> schedule t <*> schedule f
        )
      , ( "ident"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, someId) <- mustBeVec stx
            x@(Stx _ _ _) <- mustBeIdent someId
            link dest $ CoreIdentifier x
        )
      , ( "ident-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, someId, source) <- mustBeVec stx
            idDest <- schedule someId
            sourceDest <- schedule source
            link dest $ CoreIdent $ ScopedIdent idDest sourceDest
        )
      , ( "empty-list-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, source) <- mustBeVec stx
            sourceDest <- schedule source
            link dest $ CoreEmpty $ ScopedEmpty sourceDest
        )
      , ( "cons-list-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, car, cdr, source) <- mustBeVec stx
            carDest <- schedule car
            cdrDest <- schedule cdr
            sourceDest <- schedule source
            link dest $ CoreCons $ ScopedCons carDest cdrDest sourceDest
        )
      , ( "vec-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, vec, source) <- mustBeVec stx
            Stx _ _ vecItems <- mustBeVec vec
            vecDests <- traverse schedule vecItems
            sourceDest <- schedule source
            link dest $ CoreVec $ ScopedVec vecDests sourceDest
        )
      , ( "syntax-case"
        , \dest stx -> do
            Stx scs loc (_ :: Syntax, args) <- mustBeCons stx
            Stx _ _ (scrutinee, patterns) <- mustBeCons (Syntax (Stx scs loc (List args)))
            scrutDest <- schedule scrutinee
            patternDests <- traverse (mustBeVec >=> expandPatternCase) patterns
            link dest $ CoreCase scrutDest patternDests
        )
      , ( "let-syntax"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, macro, body) <- mustBeVec stx
            Stx _ _ (mName, mdef) <- mustBeVec macro
            sc <- freshScope
            m <- mustBeIdent mName
            p <- currentPhase
            let m' = addScope p m sc
            b <- freshBinding
            addBinding m' b
            macroDest <- inEarlierPhase $ do
              psc <- phaseRoot
              schedule (addScope (prior p) mdef psc)
            afterMacro b macroDest dest (addScope p body sc)
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
      addReady dest stx
      return dest

    addModulePrimitive :: Text -> (Syntax -> Expand ()) -> Expand ()
    addModulePrimitive name impl = do
      let val = EPrimModuleMacro impl
      b <- freshBinding
      -- FIXME primitive scope:
      addBinding (Stx ScopeSet.empty fakeLoc name) b
      bind b val

    addDeclPrimitive :: Text -> (DeclPtr -> Syntax -> Expand ()) -> Expand ()
    addDeclPrimitive name impl = do
      let val = EPrimDeclMacro impl
      b <- freshBinding
      -- FIXME primitive scope:
      addBinding (Stx ScopeSet.empty fakeLoc name) b
      bind b val


    addExprPrimitive :: Text -> (SplitCorePtr -> Syntax -> Expand ()) -> Expand ()
    addExprPrimitive name impl = do
      let val = EPrimMacro impl
      b <- freshBinding
      -- FIXME primitive scope:
      addBinding (Stx ScopeSet.empty fakeLoc name) b
      bind b val

    fakeLoc :: SrcLoc
    fakeLoc = SrcLoc "internals" (SrcPos 0 0) (SrcPos 0 0)

freshVar :: Expand Var
freshVar = Var <$> liftIO newUnique

readyDecls :: ModBodyPtr -> Syntax -> Expand ()
readyDecls dest (Syntax (Stx _ _ (List []))) =
  modifyState $
  \st -> st { _expanderCompletedModBody =
              _expanderCompletedModBody st <> Map.singleton dest Done
            }
readyDecls dest (Syntax (Stx scs loc (List (d:ds)))) = do
  sc <- freshScope
  restDest <- liftIO $ newModBodyPtr
  declDest <- liftIO $ newDeclPtr
  modifyState $ over expanderCompletedModBody $
    (<> Map.singleton dest (Decl declDest restDest))
  tid <- newTaskID
  p <- currentPhase
  modifyState $
    over expanderTasks $
      ((tid, MoreDecls restDest (Syntax (Stx scs loc (List (map (flip (addScope p) sc) ds)))) declDest) :)
  tid' <- newTaskID
  modifyState $
    over expanderTasks ((tid', ReadyDecl declDest (addScope p d sc)) :)

readyDecls _dest _other =
  error "TODO real error message - malformed module body"


addReady :: SplitCorePtr -> Syntax -> Expand ()
addReady dest stx = do
  p <- currentPhase
  tid <- newTaskID
  modifyState $ over expanderTasks ((tid, Ready dest p stx) :)

afterMacro :: Binding -> SplitCorePtr -> SplitCorePtr -> Syntax -> Expand ()
afterMacro b mdest dest stx = do
  tid <- newTaskID
  modifyState $
    \st -> st { _expanderTasks =
                (tid, AwaitingMacro dest (TaskAwaitMacro b [mdest] mdest stx)) :
                view expanderTasks st
              }


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
        then throwError (NoProgress (map snd newTasks))
        else expandTasks
  where
    taskIDs = Set.fromList . map fst

runTask :: (TaskID, ExpanderTask) -> Expand ()
runTask (tid, task) =
  case task of
    Ready dest p stx ->
      inPhase p (expandOneExpression dest stx)
    AwaitingSignal _dest _on _k ->
      error "Unimplemented: macro monad interpretation (unblocking)"
    AwaitingMacro dest (TaskAwaitMacro b deps mdest stx) -> do
      newDeps <- concat <$> traverse dependencies deps
      case newDeps of
        (_:_) ->
          later b dest newDeps mdest stx
        [] ->
          linkedCore mdest >>=
          \case
            Nothing -> error "Internal error - macro body not fully expanded"
            Just macroImpl -> do
              macroImplVal <- inEarlierPhase $ expandEval $ eval macroImpl
              bind b $ EUserMacro ExprMacro macroImplVal
              addReady dest stx
    ReadyDecl dest stx ->
      expandOneDeclaration dest stx
    MoreDecls dest stx waitingOn -> do
      readyYet <- view (expanderCompletedDecls . at waitingOn) <$> getState
      case readyYet of
        Nothing ->
          -- Save task for later - not ready yet
          modifyState $ over expanderTasks ((tid, task) :)
        Just _ -> do
          readyDecls dest stx

  where
    later b dest deps mdest stx = do
      tid' <- newTaskID
      modifyState $
        over expanderTasks $
          ((tid', AwaitingMacro dest (TaskAwaitMacro b deps mdest stx)) :)


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
            Id _ -> link dest (CoreVar var)
            Sig _ -> error "Impossible - signal not ident"
            Bool _ -> error "Impossible - boolean not ident"
            List xs -> expandOneExpression dest (addApp List stx xs)
            Vec xs -> expandOneExpression dest (addApp Vec stx xs)
        EIncompleteMacro mdest -> do
          tid <- newTaskID
          let todo = TaskAwaitMacro { awaitMacroBinding = b
                                    , awaitMacroDependsOn = [mdest]
                                    , awaitMacroLocation = mdest
                                    , awaitMacroSyntax = stx
                                    }
          modifyState $ over expanderTasks $ ((tid, AwaitingMacro dest todo) :)
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
                Left (_sig, _kont) -> error "Unimplemented - blocking on signals"
                Right expanded ->
                  case expanded of
                    ValueSyntax expansionResult ->
                      addReady dest (flipScope p expansionResult stepScope)
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
      Bool b -> link dest (CoreBool b)
      Id _ -> error "Impossible happened - identifiers are identifier-headed!"

-- | Insert a function application marker with a lexical context from
-- the original expression
addApp :: (forall a . [a] -> ExprF a) -> Syntax -> [Syntax] -> Syntax
addApp ctor (Syntax (Stx scs loc _)) args =
  Syntax (Stx scs loc (ctor (app : args)))
  where
    app = Syntax (Stx scs loc (Id "#%app"))

expandOneDeclaration :: DeclPtr -> Syntax -> Expand ()
expandOneDeclaration dest stx
  | Just ident <- identifierHeaded stx = do
      b <- resolve ident
      v <- getEValue b
      case v of
        EPrimMacro _ ->
          throwError $ InternalError "Current context won't accept expressions"
        EPrimModuleMacro _ ->
          throwError $ InternalError "Current context won't accept modules"
        EPrimDeclMacro impl ->
          impl dest stx
        EVarMacro _ ->
          throwError $ InternalError "Current context won't accept expressions"
        EUserMacro _ _impl ->
          error "Unimplemented: user-defined macros - decl context"
        EIncompleteMacro _ ->
          error "Unimplemented: user-defined macros - decl context - incomplete"
  | otherwise =
    throwError $ InternalError "All declarations should be identifier-headed"


-- | Link the destination to a literal signal object
expandLiteralSignal :: SplitCorePtr -> Signal -> Expand ()
expandLiteralSignal dest signal = link dest (CoreSignal signal)

interpretMacroAction :: MacroAction -> Expand (Either (Signal, [Closure]) Value)
interpretMacroAction (MacroActionPure value) = do
  pure $ Right value
interpretMacroAction (MacroActionBind macroAction closure) = do
  interpretMacroAction macroAction >>= \case
    Left (signal, closures) -> do
      pure $ Left (signal, closures ++ [closure])
    Right boundResult -> do
      phase <- view expanderPhase
      s <- getState
      let env = fromMaybe Env.empty
                          (s ^. expanderEnvironments . at phase)
      evalResult <- liftIO
                  $ runExceptT
                  $ flip runReaderT env
                  $ runEval
                  $ apply closure boundResult
      case evalResult of
        Left evalError -> do
          throwError $ MacroEvaluationError evalError
        Right value ->
          case value of
            ValueMacroAction act -> interpretMacroAction act
            other -> throwError $ ValueNotMacro other
interpretMacroAction (MacroActionSyntaxError syntaxError) = do
  throwError $ MacroRaisedSyntaxError syntaxError
interpretMacroAction (MacroActionSendSignal signal) = do
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

