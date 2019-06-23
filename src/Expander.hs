{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, RecordWildCards #-}
module Expander where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Data.IORef
import Data.Foldable

import Data.Unique
import Data.List.Extra
import Data.Map (Map)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural

import Core
import PartialCore
import Signals
import Syntax
import Value

newtype Binding = Binding Unique
  deriving (Eq, Ord)

type BindingTable = Map Text [(ScopeSet, Binding)]

freshBinding :: Expand Binding
freshBinding = Binding <$> liftIO newUnique

data ExpansionErr
  = Ambiguous Text
  | Unknown (Stx Text)
  | NotIdentifier Syntax
  | NotEmpty Syntax
  | NotCons Syntax
  | NotRightLength Natural Syntax

newtype Phase = Phase Natural
  deriving (Eq, Ord, Show)

data ExpanderContext = ExpanderContext
  { expanderState :: IORef ExpanderState
  , expanderPhase :: !Phase
  }

data ExpanderState = ExpanderState
  { expanderReceivedSignals :: !(Set.Set Signal)
  , expanderEnvironments :: !(Map.Map Phase Env)
  , expanderNextScope :: !Scope
  , expanderBindingTable :: !BindingTable
  , expanderExpansionEnv :: !ExpansionEnv
  , expanderTasks :: [(Unique, ExpanderTask)]
  }

initExpanderState :: ExpanderState
initExpanderState = ExpanderState
  { expanderReceivedSignals = Set.empty
  , expanderEnvironments = Map.empty
  , expanderNextScope = Scope 0
  , expanderBindingTable = Map.empty
  , expanderExpansionEnv = ExpansionEnv
  , expanderTasks = []
  }

data ExpansionEnv = ExpansionEnv -- TODO

newtype Expand a = Expand
  { runExpand :: ReaderT ExpanderContext (ExceptT ExpansionErr IO) a
  }
  deriving (Functor, Applicative, Monad, MonadError ExpansionErr, MonadIO)

data ExpanderTask
  = Ready Syntax
  | Blocked Signal Value -- the value is the continuation

expanderContext :: Expand ExpanderContext
expanderContext = Expand ask

getState :: Expand ExpanderState
getState = expanderState <$> expanderContext >>= liftIO . readIORef

modifyState :: (ExpanderState -> ExpanderState) -> Expand ()
modifyState f = do
  st <- expanderState <$> expanderContext
  liftIO (modifyIORef st f)

freshScope :: Expand Scope
freshScope = do
  sc <- expanderNextScope <$> getState
  modifyState (\st -> st { expanderNextScope = nextScope (expanderNextScope st) })
  return sc


bindingTable :: Expand BindingTable
bindingTable = expanderBindingTable <$> getState

addBinding :: Text -> ScopeSet -> Binding -> Expand ()
addBinding name scs b = do
  -- Note: assumes invariant that a name-scopeset pair is never mapped
  -- to two bindings. That would indicate a bug in the expander but
  -- this code doesn't catch that.
  modifyState $
    \st -> st { expanderBindingTable =
                Map.insertWith (<>) name [(scs, b)] $
                expanderBindingTable st
              }

allMatchingBindings :: Text -> ScopeSet -> Expand [(ScopeSet, Binding)]
allMatchingBindings x scs = do
  bindings <- bindingTable
  return $
    filter (flip Set.isSubsetOf scs . fst) $
    fromMaybe [] (Map.lookup x bindings)

checkUnambiguous :: Text -> ScopeSet -> [ScopeSet] -> Syntax -> Expand ()
checkUnambiguous x best candidates blame =
  let bestSize = Set.size best
      candidateSizes = map Set.size candidates
  in
    if length (filter (== bestSize) candidateSizes) > 1
      then throwError (Ambiguous x)
      else return ()

resolve :: Syntax -> Expand Binding
resolve stx@(Syntax (Stx scs srcLoc (Id x))) = do
  bs <- allMatchingBindings x scs
  case bs of
    [] -> throwError (Unknown (Stx scs srcLoc x))
    candidates ->
      let best = maximumOn (Set.size . fst) candidates
      in checkUnambiguous x (fst best) (map fst candidates) stx *>
         return (snd best)
resolve other = throwError (NotIdentifier other)

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


data SplitCore = SplitCore
  { splitCoreRoot        :: CoreF Unique
  , splitCoreDescendants :: Map Unique (CoreF Unique)
  }

zonk :: SplitCore -> PartialCore
zonk (SplitCore {..}) = PartialCore $ fmap go splitCoreRoot
  where
    go :: Unique -> Maybe PartialCore
    go unique = do
      child <- Map.lookup unique splitCoreDescendants
      pure $ zonk $ SplitCore
        { splitCoreRoot        = child
        , splitCoreDescendants = splitCoreDescendants
        }

unzonk :: PartialCore -> IO SplitCore
unzonk partialCore = do
  (root, children) <- runWriterT $ do
    traverse go (unPartialCore partialCore)
  pure $ SplitCore root children
  where
    go :: Maybe PartialCore
       -> WriterT (Map Unique (CoreF Unique))
                  IO
                  Unique
    go maybePartialCore = do
      unique <- liftIO $ newUnique
      for_ maybePartialCore $ \partialCore -> do
        SplitCore {..} <- liftIO $ unzonk partialCore
        tell $ Map.singleton unique splitCoreRoot
        tell splitCoreDescendants
      pure unique

expand :: Syntax -> Expand SplitCore
expand stx = undefined
