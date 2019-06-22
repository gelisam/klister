{-# LANGUAGE GeneralizedNewtypeDeriving, RecordWildCards #-}
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

import Core
import PartialCore
import Syntax

newtype Binding = Binding Unique
  deriving (Eq, Ord)

type BindingTable = Map Text [(ScopeSet, Binding)]

freshBinding :: Expand Binding
freshBinding = Binding <$> liftIO newUnique

data ExpansionErr
  = Ambiguous Text
  | Unknown (Stx Text)
  | NotIdentifier Syntax

newtype Expand a = Expand
  { runExpand :: ReaderT (IORef BindingTable) (ExceptT ExpansionErr IO) a
  }
  deriving (Functor, Applicative, Monad, MonadError ExpansionErr, MonadIO)

bindingTable :: Expand (IORef BindingTable)
bindingTable = Expand ask

addBinding :: Text -> ScopeSet -> Binding -> Expand ()
addBinding name scs b = do
  table <- bindingTable
  -- Note: assumes invariant that a name-scopeset pair is never mapped
  -- to two bindings. That would indicate a bug in the expander but
  -- this code doesn't catch that.
  liftIO (modifyIORef table (Map.insertWith (<>) name [(scs, b)]))

allMatchingBindings :: Text -> ScopeSet -> Expand [(ScopeSet, Binding)]
allMatchingBindings x scs = do
  table <- bindingTable
  bindings <- liftIO $ readIORef table
  return $
    filter (flip Set.isSubsetOf scs . fst) $
    fromMaybe [] (Map.lookup x bindings)

resolve :: Syntax -> Expand Binding
resolve (Syntax (Stx scs srcLoc (Id x))) = do
  bs <- allMatchingBindings x scs
  case bs of
    [] -> throwError (Unknown (Stx scs srcLoc x))
    candidates ->
      let best = maximumOn (Set.size . fst) candidates
      in undefined -- TODO check unambiguous, then return the binding object
resolve other = throwError (NotIdentifier other)

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
