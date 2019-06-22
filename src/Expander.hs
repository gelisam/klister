{-# LANGUAGE RecordWildCards #-}
module Expander where

import Control.Monad.Writer
import Data.Unique
import Data.Map (Map)
import Data.Maybe
import qualified Data.Map as Map

import Core


data SplitCore = SplitCore
  { splitCoreRoot     :: CoreF Unique
  , splitCoreChildren :: Map Unique (CoreF Unique)
  }

zonk :: SplitCore -> Core
zonk (SplitCore {..}) = Core $ fmap go splitCoreRoot
  where
    go :: Unique -> Core
    go unique = Core
              $ fmap go
              $ fromMaybe (error $ "zonk: child missing: " ++ show (hashUnique unique))
              $ Map.lookup unique splitCoreChildren

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
      tell splitCoreChildren
      pure unique
