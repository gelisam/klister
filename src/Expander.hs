{-# LANGUAGE RecordWildCards #-}
module Expander where

import Control.Monad.Writer
import Data.Foldable
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
