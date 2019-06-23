{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, RecordWildCards, TemplateHaskell, ViewPatterns #-}
module SplitCore where

import Control.Lens hiding (List, children)
import Control.Monad.Except
import Control.Monad.Writer

import Data.Unique
import Data.Map (Map)
import qualified Data.Map as Map

import Core
import PartialCore


data SplitCore = SplitCore
  { _splitCoreRoot        :: Unique
  , _splitCoreDescendants :: Map Unique (CoreF Unique)
  }
makeLenses ''SplitCore

zonk :: SplitCore -> PartialCore
zonk (SplitCore {..}) = PartialCore $ go _splitCoreRoot
  where
    go :: Unique -> Maybe (CoreF PartialCore)
    go unique = do
      this <- Map.lookup unique _splitCoreDescendants
      return (fmap (PartialCore . go) this)

unzonk :: PartialCore -> IO SplitCore
unzonk partialCore = do
  root <- newUnique
  ((), childMap) <- runWriterT $ go root (unPartialCore partialCore)
  return $ SplitCore root childMap
  where
    go ::
      Unique -> Maybe (CoreF PartialCore) ->
      WriterT (Map Unique (CoreF Unique)) IO ()
    go _     Nothing = pure ()
    go place (Just c) = do
      children <- flip traverse c $ \p -> do
        here <- liftIO newUnique
        go here (unPartialCore p)
        pure here
      tell $ Map.singleton place children
