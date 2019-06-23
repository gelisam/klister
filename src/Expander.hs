{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, OverloadedStrings, RecordWildCards, RankNTypes, TemplateHaskell, ViewPatterns #-}
module Expander where

import Control.Lens hiding (List, children)
import Control.Monad.Except
import Control.Monad.Reader
import Data.IORef

import Data.Unique
import Data.List.Extra
import Data.Map (Map)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Numeric.Natural

import Core
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
  | NotIdentifier Syntax
  | NotEmpty Syntax
  | NotCons Syntax
  | NotRightLength Natural Syntax
  | InternalError String

newtype Phase = Phase Natural
  deriving (Eq, Ord, Show)

data ExpanderContext = ExpanderContext
  { _expanderState :: IORef ExpanderState
  , _expanderPhase :: !Phase
  }

data ExpanderState = ExpanderState
  { _expanderReceivedSignals :: !(Set.Set Signal)
  , _expanderEnvironments :: !(Map.Map Phase Env)
  , _expanderNextScope :: !Scope
  , _expanderBindingTable :: !BindingTable
  , _expanderExpansionEnv :: !ExpansionEnv
  , _expanderTasks :: [(Unique, ExpanderTask)]
  }

initExpanderState :: ExpanderState
initExpanderState = ExpanderState
  { _expanderReceivedSignals = Set.empty
  , _expanderEnvironments = Map.empty
  , _expanderNextScope = Scope 0
  , _expanderBindingTable = Map.empty
  , _expanderExpansionEnv = ExpansionEnv mempty
  , _expanderTasks = []
  }

data EValue
  = EPrimMacro (Syntax -> Expand SplitCore) -- ^ For "special forms"
  | EVarMacro !Unique -- ^ For bound variables (the Unique is the binding site of the var)
  | EUserMacro !SyntacticCategory !Value -- ^ For user-written macros

data SyntacticCategory = Module | Declaration | Expression

newtype ExpansionEnv = ExpansionEnv (Map.Map Binding EValue)

newtype Expand a = Expand
  { runExpand :: ReaderT ExpanderContext (ExceptT ExpansionErr IO) a
  }
  deriving (Functor, Applicative, Monad, MonadError ExpansionErr, MonadIO)

data ExpanderTask
  = Ready Syntax
  | Blocked Signal Value -- the value is the continuation

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


bindingTable :: Expand BindingTable
bindingTable = view expanderBindingTable <$> getState

addBinding :: Text -> ScopeSet -> Binding -> Expand ()
addBinding name scs b = do
  -- Note: assumes invariant that a name-scopeset pair is never mapped
  -- to two bindings. That would indicate a bug in the expander but
  -- this code doesn't catch that.
  modifyState $
    \st -> st { _expanderBindingTable =
                Map.insertWith (<>) name [(scs, b)] $
                view expanderBindingTable st
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

instance MustBeVec (Syntax, Syntax, Syntax) where
  mustBeVec (Syntax (Stx scs srcloc (Vec [x, y, z]))) = return (Stx scs srcloc (x, y, z))
  mustBeVec other = throwError (NotRightLength 3 other)

instance MustBeVec (Syntax, Syntax, Syntax, Syntax) where
  mustBeVec (Syntax (Stx scs srcloc (Vec [w, x, y, z]))) = return (Stx scs srcloc (w, x, y, z))
  mustBeVec other = throwError (NotRightLength 4 other)

instance MustBeVec (Syntax, Syntax, Syntax, Syntax, Syntax) where
  mustBeVec (Syntax (Stx scs srcloc (Vec [v, w, x, y, z]))) =
    return (Stx scs srcloc (v, w, x, y, z))
  mustBeVec other = throwError (NotRightLength 5 other)


identifierHeaded :: Syntax -> Maybe Ident
identifierHeaded (Syntax (Stx scs srcloc (Id x))) = Just (Stx scs srcloc x)
identifierHeaded (Syntax (Stx _ _ (List (h:_))))
  | (Syntax (Stx scs srcloc (Id x))) <- h = Just (Stx scs srcloc x)
identifierHeaded (Syntax (Stx _ _ (Vec (h:_))))
  | (Syntax (Stx scs srcloc (Id x))) <- h = Just (Stx scs srcloc x)
identifierHeaded _ = Nothing

expandExpression :: Syntax -> Expand SplitCore
expandExpression stx
  | Just ident <- identifierHeaded stx = do
      b <- resolve ident
      v <- getEValue b
      case v of
        EPrimMacro impl -> impl stx
        EVarMacro var ->
          do e <- liftIO $ newUnique
             return $ SplitCore { _splitCoreRoot = e
                                , _splitCoreDescendants = Map.singleton e (CoreVar var)
                                }
        EUserMacro _ _impl ->
          error "Unimplemented"
  | otherwise =
    case syntaxE stx of
      Vec xs -> expandExpression (addApp Vec stx xs)
      List xs -> expandExpression (addApp List stx xs)
      Id _ -> error "Impossible happened - identifiers are identifier-headed!"

-- | Insert a function application marker with a lexical context from
-- the original expression
addApp :: (forall a . [a] -> ExprF a) -> Syntax -> [Syntax] -> Syntax
addApp ctor (Syntax (Stx scs loc _)) args =
  Syntax (Stx scs loc (ctor (app : args)))
  where
    app = Syntax (Stx scs loc (Id "#%app"))

