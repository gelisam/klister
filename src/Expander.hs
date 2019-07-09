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
module Expander where

import Control.Lens hiding (List, children)
import Control.Monad.Except
import Control.Monad.Reader
import Data.IORef

import Data.Unique
import Data.List.Extra
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural

import Core
import Env
import Evaluator
import PartialCore
import Scope
import ScopeSet (ScopeSet)
import Signals
import SplitCore
import Syntax
import Value
import qualified ScopeSet


newtype Binding = Binding Unique
  deriving (Eq, Ord)

type BindingTable = Map Text [(ScopeSet, Binding)]

data ExpansionErr
  = Ambiguous Ident
  | Unknown (Stx Text)
  | NoProgress [ExpanderTask]
  | NotIdentifier Syntax
  | NotEmpty Syntax
  | NotCons Syntax
  | NotRightLength Natural Syntax
  | NotVec Syntax
  | UnknownPattern Syntax
  | MacroRaisedSyntaxError (SyntaxError Syntax)
  | MacroEvaluationError EvalError
  | ValueNotMacro Value
  | ValueNotSyntax Value
  | InternalError String
  deriving (Show)


expansionErrText :: ExpansionErr -> Text
expansionErrText (Ambiguous x) = "Ambiguous identifier " <> T.pack (show x)
expansionErrText (Unknown x) = "Unknown: " <> T.pack (show x)
expansionErrText (NoProgress tasks) =
  "No progress was possible: " <> T.pack (show tasks)
expansionErrText (NotIdentifier stx) =
  "Not an identifier: " <> syntaxText stx
expansionErrText (NotEmpty stx) = "Expected (), but got " <> syntaxText stx
expansionErrText (NotCons stx) =
  "Expected non-empty parens, but got " <> syntaxText stx
expansionErrText (NotRightLength len stx) =
  "Expected " <> T.pack (show len) <>
  " entries between square brackets, but got " <> syntaxText stx
expansionErrText (NotVec stx) =
  "Expected square-bracketed vec but got " <> syntaxText stx
expansionErrText (UnknownPattern stx) =
  "Unknown pattern " <> syntaxText stx
expansionErrText (MacroRaisedSyntaxError err) =
  "Syntax error from macro: " <> T.pack (show err)
expansionErrText (MacroEvaluationError err) =
  "Error during macro evaluation: " <> T.pack (show err)
expansionErrText (ValueNotMacro val) =
  "Not a macro monad value: " <> valueText val
expansionErrText (ValueNotSyntax val) =
  "Not a syntax object: " <> valueText val
expansionErrText (InternalError str) =
  "Internal error during expansion! This is a bug in the implementation." <> T.pack str


newtype Phase = Phase Natural
  deriving (Eq, Ord, Show)

data ExpanderContext = ExpanderContext
  { _expanderState :: IORef ExpanderState
  , _expanderPhase :: !Phase
  }

mkInitContext :: IO ExpanderContext
mkInitContext = do
  st <- newIORef initExpanderState
  return $ ExpanderContext { _expanderState = st
                           , _expanderPhase = Phase 0
                           }

data ExpanderState = ExpanderState
  { _expanderReceivedSignals :: !(Set.Set Signal)
  , _expanderEnvironments :: !(Map.Map Phase (Env Value))
  , _expanderNextScope :: !Scope
  , _expanderBindingTable :: !BindingTable
  , _expanderExpansionEnv :: !ExpansionEnv
  , _expanderTasks :: [(Unique, ExpanderTask)]
  , _expanderComplete :: !(Map.Map Unique (CoreF Unique))
  }

initExpanderState :: ExpanderState
initExpanderState = ExpanderState
  { _expanderReceivedSignals = Set.empty
  , _expanderEnvironments = Map.empty
  , _expanderNextScope = Scope 0
  , _expanderBindingTable = Map.empty
  , _expanderExpansionEnv = mempty
  , _expanderTasks = []
  , _expanderComplete = Map.empty
  }

data EValue
  = EPrimMacro (Unique -> Syntax -> Expand ()) -- ^ For "special forms"
  | EVarMacro !Var -- ^ For bound variables (the Unique is the binding site of the var)
  | EUserMacro !SyntacticCategory !Value -- ^ For user-written macros

data SyntacticCategory = Module | Declaration | Expression

newtype ExpansionEnv = ExpansionEnv (Map.Map Binding EValue)
  deriving (Semigroup, Monoid)

newtype Expand a = Expand
  { runExpand :: ReaderT ExpanderContext (ExceptT ExpansionErr IO) a
  }
  deriving (Functor, Applicative, Monad, MonadError ExpansionErr, MonadIO, MonadReader ExpanderContext)

execExpand :: Expand a -> ExpanderContext -> IO (Either ExpansionErr a)
execExpand act ctx = runExceptT $ runReaderT (runExpand act) ctx

data TaskAwaitMacro = TaskAwaitMacro
  { awaitMacroDependsOn :: [Unique] -- the [Unique] is the collection of open problems that represent the macro's expansion. When it's empty, the macro is available.
  , awaitMacroLocation :: Unique -- the destination into which the macro will be expanded.
  , awaitMacroSyntax :: Syntax -- the syntax object to be expanded once the macro is available
  }

instance Show TaskAwaitMacro where
  show (TaskAwaitMacro _ _ stx) = "TaskAwaitMacro " ++ T.unpack (syntaxText stx)


data ExpanderTask
  = Ready Syntax
  | AwaitingSignal Signal Value -- the value is the continuation
  | AwaitingMacro TaskAwaitMacro --   at the second Unique.


instance Show ExpanderTask where
  show (Ready stx) = "Ready " ++ T.unpack (syntaxText stx)
  show (AwaitingSignal on _k) = "AwaitingSignal (" ++ show on ++ ")"
  show (AwaitingMacro t) = "AwaitingMacro (" ++ show t ++ ")"


makePrisms ''Binding
makePrisms ''ExpansionErr
makePrisms ''Phase
makeLenses ''ExpanderContext
makeLenses ''ExpanderState
makePrisms ''EValue
makePrisms ''SyntacticCategory
makePrisms ''ExpansionEnv
makePrisms ''ExpanderTask


freshBinding :: Expand Binding
freshBinding = Binding <$> liftIO newUnique

getEValue :: Binding -> Expand EValue
getEValue b = do
  ExpansionEnv env <- view expanderExpansionEnv <$> getState
  case Map.lookup b env of
    Just v -> return v
    Nothing -> throwError (InternalError "No such binding")

expanderContext :: Expand ExpanderContext
expanderContext = Expand ask

getState :: Expand ExpanderState
getState = view expanderState <$> expanderContext >>= liftIO . readIORef

modifyState :: (ExpanderState -> ExpanderState) -> Expand ()
modifyState f = do
  st <- view expanderState <$> expanderContext
  liftIO (modifyIORef st f)

freshScope :: Expand Scope
freshScope = do
  sc <- view expanderNextScope <$> getState
  modifyState (\st -> st { _expanderNextScope = nextScope (view expanderNextScope st) })
  return sc

link :: Unique -> CoreF Unique -> Expand ()
link dest layer =
  modifyState $
  \st -> st { _expanderComplete =
              _expanderComplete st <> Map.singleton dest layer
            }

linkStatus :: Unique -> Expand (Maybe (CoreF Unique))
linkStatus slot = do
  complete <- view expanderComplete <$> getState
  return $ Map.lookup slot complete

linkedCore :: Unique -> Expand (Maybe Core)
linkedCore slot =
  runPartialCore . unsplit . SplitCore slot . view expanderComplete <$>
  getState


getTasks :: Expand [(Unique, ExpanderTask)]
getTasks = view expanderTasks <$> getState

clearTasks :: Expand ()
clearTasks = modifyState $ \st -> st { _expanderTasks = [] }

currentPhase :: Expand Phase
currentPhase = Expand $ view expanderPhase <$> ask

inEarlierPhase :: Expand a -> Expand a
inEarlierPhase act =
  Expand $
  local (over expanderPhase $
         \(Phase p) -> Phase (1 + p)) $
  runExpand act

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
  \st ->
    let ExpansionEnv env = view expanderExpansionEnv st
    in st { _expanderExpansionEnv =
            ExpansionEnv $ Map.insert b v env
          }

allMatchingBindings :: Text -> ScopeSet -> Expand [(ScopeSet, Binding)]
allMatchingBindings x scs = do
  bindings <- bindingTable
  return $
    filter (flip ScopeSet.isSubsetOf scs . fst) $
    fromMaybe [] (Map.lookup x bindings)

checkUnambiguous :: ScopeSet -> [ScopeSet] -> Ident -> Expand ()
checkUnambiguous best candidates blame =
  let bestSize = ScopeSet.size best
      candidateSizes = map ScopeSet.size candidates
  in
    if length (filter (== bestSize) candidateSizes) > 1
      then throwError (Ambiguous blame)
      else return ()

resolve :: Ident -> Expand Binding
resolve stx@(Stx scs srcLoc x) = do
  bs <- allMatchingBindings x scs
  case bs of
    [] -> throwError (Unknown (Stx scs srcLoc x))
    candidates ->
      let best = maximumOn (ScopeSet.size . fst) candidates
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


initializeExpansionEnv :: Expand ()
initializeExpansionEnv =
  traverse (uncurry addPrimitive) prims *>
  pure ()

  where
    prims :: [(Text, Unique -> Syntax -> Expand ())]
    prims =
      [ ( "oops"
        , \ _ stx -> throwError (InternalError $ "oops" ++ show stx)
        )
      , ( "lambda"
        , \ dest stx -> do
            Stx _ _ (_, arg, body) <- mustBeVec stx
            Stx _ _ theArg <- mustBeVec arg
            (sc, arg', coreArg) <- prepareVar theArg
            bodyDest <- schedule $ addScope body sc
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
      , ( "quote"
        , \dest stx -> do
            Stx _ _ (_ :: Syntax, quoted) <- mustBeVec stx
            link dest $ CoreSyntax quoted
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
            let m' = addScope m sc
            b <- freshBinding
            addBinding m' b
            macroDest <- schedule mdef
            afterMacro macroDest dest (addScope body sc)
        )
      ]

    expandPatternCase :: Stx (Syntax, Syntax) -> Expand (Pattern, Unique)
    -- TODO match case keywords hygienically
    expandPatternCase (Stx _ _ (lhs, rhs)) =
      case lhs of
        Syntax (Stx _ _ (Vec [Syntax (Stx _ _ (Id "ident")),
                              patVar])) -> do
          (sc, x', var) <- prepareVar patVar
          let rhs' = addScope rhs sc
          rhsDest <- schedule rhs'
          let patOut = PatternIdentifier x' var
          return (patOut, rhsDest)
        Syntax (Stx _ _ (Vec [Syntax (Stx _ _ (Id "vec")),
                              Syntax (Stx _ _ (Vec vars))])) -> do
          varInfo <- traverse prepareVar vars
          let rhs' = foldr (flip addScope) rhs [sc | (sc, _, _) <- varInfo]
          rhsDest <- schedule rhs'
          let patOut = PatternVec [(ident, var) | (_, ident, var) <- varInfo]
          return (patOut, rhsDest)
        Syntax (Stx _ _ (Vec [Syntax (Stx _ _ (Id "cons")),
                              car,
                              cdr])) -> do
          (sc, car', carVar) <- prepareVar car
          (sc', cdr', cdrVar) <- prepareVar cdr
          let rhs' = addScope (addScope rhs sc) sc'
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
      let x' = addScope x sc
      b <- freshBinding
      addBinding x' b
      var <- freshVar
      bind b (EVarMacro var)
      return (sc, x', var)


    schedule :: Syntax -> Expand Unique
    schedule stx = do
      dest <- liftIO newUnique
      addReady dest stx
      return dest

    addPrimitive :: Text -> (Unique -> Syntax -> Expand ()) -> Expand ()
    addPrimitive name impl = do
      let val = EPrimMacro impl
      b <- freshBinding
      -- FIXME primitive scope:
      addBinding (Stx ScopeSet.empty fakeLoc name) b
      bind b val

    fakeLoc :: SrcLoc
    fakeLoc = SrcLoc "internals" (SrcPos 0 0) (SrcPos 0 0)

freshVar :: Expand Var
freshVar = Var <$> liftIO newUnique

addReady :: Unique -> Syntax -> Expand ()
addReady dest stx =
  modifyState $
  \st -> st { _expanderTasks = (dest, Ready stx) : view expanderTasks st
            }

afterMacro :: Unique -> Unique -> Syntax -> Expand ()
afterMacro mdest dest stx =
  modifyState $
  \st -> st { _expanderTasks =
              (dest, AwaitingMacro (TaskAwaitMacro [mdest] mdest stx)) :
              view expanderTasks st
            }


identifierHeaded :: Syntax -> Maybe Ident
identifierHeaded (Syntax (Stx scs srcloc (Id x))) = Just (Stx scs srcloc x)
identifierHeaded (Syntax (Stx _ _ (List (h:_))))
  | (Syntax (Stx scs srcloc (Id x))) <- h = Just (Stx scs srcloc x)
identifierHeaded (Syntax (Stx _ _ (Vec (h:_))))
  | (Syntax (Stx scs srcloc (Id x))) <- h = Just (Stx scs srcloc x)
identifierHeaded _ = Nothing

expandExpr :: Syntax -> Expand SplitCore
expandExpr stx = do
  dest <- liftIO $ newUnique
  modifyState $ \st -> st {_expanderTasks = [(dest, Ready stx)]}
  expandTasks
  children <- _expanderComplete <$> getState
  return $ SplitCore {_splitCoreRoot = dest
                     , _splitCoreDescendants = children
                     }

expandTasks :: Expand ()
expandTasks = do
  tasks <- getTasks
  case tasks of
    [] -> return ()
    more -> do
      clearTasks
      forM_ more runTask
      _newTasks <- getTasks
      -- TODO: Fix cycle detection

      -- The problem here is that multi-step expansion leaves the same
      -- destinations behind in the task queue, even though work has
      -- been done. We can't compare tasks for equality because they
      -- contain closures, and we probably want to go higher-order on
      -- those, or we want things like network connection handles in
      -- values.

      -- The solution may be to annotate each task with a Unique, and
      -- compare those for task equality. This would capture progress.

      -- if tasks == newTasks
      --   then throwError (NoProgress (map snd newTasks))
      --   else expandTasks
      expandTasks

runTask :: (Unique, ExpanderTask) -> Expand ()
runTask (dest, task) =
  case task of
    Ready stx -> expandOneExpression dest stx
    AwaitingSignal _on _k -> error "Unimplemented: macro monad interpretation (unblocking)"
    AwaitingMacro (TaskAwaitMacro deps mdest stx) -> do
      newDeps <- concat <$> traverse dependencies deps
      case newDeps of
        (_:_) ->
          later newDeps mdest stx
        [] ->
          linkedCore mdest >>=
          \case
            Nothing -> error "Internal error - macro body not fully expanded"
            Just macroImpl -> do
              let macroExpr = Core $ CoreApp macroImpl (Core $ CoreSyntax stx)
              macroVal <- inEarlierPhase $ expandEval $ eval macroExpr
              case macroVal of
                ValueMacroAction act -> do
                  res <- interpretMacroAction act
                  case res of
                    Left (_sig, _kont) -> error "Unimplemented - blocking on signals"
                    Right v ->
                      case v of
                        ValueSyntax expansionResult ->
                          addReady dest expansionResult
                        other -> throwError $ ValueNotSyntax other
                other ->
                  throwError $ ValueNotMacro other

  where
    later deps mdest stx =
      modifyState $
      \st -> st { _expanderTasks =
                  (dest, AwaitingMacro (TaskAwaitMacro deps mdest stx)) :
                  view expanderTasks st
                }


-- | Compute the dependencies of a particular slot. The dependencies
-- are the un-linked child slots. If there are no dependencies, then
-- the sub-expression is complete. If the slot is not linked then it
-- depends on itself.
dependencies :: Unique -> Expand [Unique]
dependencies slot =
  linkStatus slot >>=
  \case
    Nothing -> pure [slot]
    Just c -> foldMap id <$> traverse dependencies c

expandOneExpression :: Unique -> Syntax -> Expand ()
expandOneExpression dest stx
  | Just ident <- identifierHeaded stx = do
      b <- resolve ident
      v <- getEValue b
      case v of
        EPrimMacro impl -> impl dest stx
        EVarMacro var ->
          case syntaxE stx of
            Id _ -> link dest (CoreVar var)
            Sig _ -> error "Impossible - signal not ident"
            List xs -> expandOneExpression dest (addApp List stx xs)
            Vec xs -> expandOneExpression dest (addApp Vec stx xs)
        EUserMacro _ _impl ->
          error "Unimplemented: user-defined macros"
  | otherwise =
    case syntaxE stx of
      Vec xs -> expandOneExpression dest (addApp Vec stx xs)
      List xs -> expandOneExpression dest (addApp List stx xs)
      Sig s -> expandLiteralSignal dest s
      Id _ -> error "Impossible happened - identifiers are identifier-headed!"

-- | Insert a function application marker with a lexical context from
-- the original expression
addApp :: (forall a . [a] -> ExprF a) -> Syntax -> [Syntax] -> Syntax
addApp ctor (Syntax (Stx scs loc _)) args =
  Syntax (Stx scs loc (ctor (app : args)))
  where
    app = Syntax (Stx scs loc (Id "#%app"))

-- | Link the destination to a literal signal object
expandLiteralSignal :: Unique -> Signal -> Expand ()
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
        Right value -> pure $ Right value
interpretMacroAction (MacroActionSyntaxError syntaxError) = do
  throwError $ MacroRaisedSyntaxError syntaxError
interpretMacroAction (MacroActionSendSignal signal) = do
  pure $ Left (signal, [])
