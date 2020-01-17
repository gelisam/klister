{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module SplitCore where

import Control.Lens hiding (children)
import Control.Monad.Except
import Control.Monad.Writer

import Data.Functor (($>))
import Data.Unique
import Data.Map (Map)
import qualified Data.Map as Map

import Core
import PartialCore

newtype SplitCorePtr = SplitCorePtr Unique
  deriving (Eq, Ord)

instance Show SplitCorePtr where
  show (SplitCorePtr u) = "(SplitCorePtr " ++ show (hashUnique u) ++ ")"

newSplitCorePtr :: IO SplitCorePtr
newSplitCorePtr = SplitCorePtr <$> newUnique

data SplitCore = SplitCore
  { _splitCoreRoot        :: SplitCorePtr
  , _splitCoreDescendants :: Map SplitCorePtr (CoreF SplitCorePtr)
  }
  deriving Show
makeLenses ''SplitCore

unsplit :: SplitCore -> PartialCore
unsplit (SplitCore {..}) = PartialCore $ go _splitCoreRoot
  where
    go :: SplitCorePtr -> Maybe (CoreF PartialCore)
    go ptr = do
      this <- Map.lookup ptr _splitCoreDescendants
      return (fmap (PartialCore . go) this)

split :: PartialCore -> IO SplitCore
split partialCore = do
  root <- newSplitCorePtr
  ((), childMap) <- runWriterT $ go root (unPartialCore partialCore)
  return $ SplitCore root childMap
  where
    go ::
      SplitCorePtr -> Maybe (CoreF PartialCore) ->
      WriterT (Map SplitCorePtr (CoreF SplitCorePtr)) IO ()
    go _     Nothing = pure ()
    go place (Just c) = do
      children <- flip traverse c $ \p -> do
        here <- liftIO newSplitCorePtr
        go here (unPartialCore p)
        pure here
      tell $ Map.singleton place children

getRoot :: SplitCore -> Maybe (CoreF SplitCorePtr)
getRoot splitCore =
  Map.lookup (_splitCoreRoot splitCore) (_splitCoreDescendants splitCore)

subtree :: SplitCore -> SplitCorePtr -> Maybe SplitCore
subtree splitCore splitCorePtr =
  let descendants = _splitCoreDescendants splitCore
  in Map.lookup splitCorePtr descendants $>
       SplitCore splitCorePtr (Map.delete (_splitCoreRoot splitCore) descendants)
