{-# LANGUAGE RecordWildCards #-}
module Expander where

import Control.Monad.Writer
import Data.Unique
import Data.Map (Map)
import Data.Maybe
import qualified Data.Map as Map

import Core
import PartialCore


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

unzonk :: Core -> IO SplitCore
unzonk core = do
  (root, children) <- runWriterT $ do
    traverse go (unCore core)
  pure $ SplitCore root children
  where
    go :: Core -> WriterT (Map Unique (CoreF Unique))
                          IO
                          Unique
    go core = do
      unique <- liftIO $ newUnique
      SplitCore {..} <- liftIO $ unzonk core
      tell $ Map.singleton unique splitCoreRoot
      tell splitCoreDescendants
      pure unique
