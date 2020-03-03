{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module SplitCore where

import Control.Lens hiding (children)
import Control.Monad.Except
import Control.Monad.Writer
import Data.Bitraversable
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

newtype PatternPtr = PatternPtr Unique
  deriving (Eq, Ord)

instance Show PatternPtr where
  show (PatternPtr u) = "(PatternPtr " ++ show (hashUnique u) ++ ")"

newPatternPtr :: IO PatternPtr
newPatternPtr = PatternPtr <$> newUnique

data SplitCore = SplitCore
  { _splitCoreRoot        :: SplitCorePtr
  , _splitCoreDescendants :: Map SplitCorePtr (CoreF PatternPtr SplitCorePtr)
  , _splitCorePatterns    :: Map PatternPtr ConstructorPattern
  }
makeLenses ''SplitCore

unsplit :: SplitCore -> PartialCore
unsplit (SplitCore {..}) = PartialCore $ go _splitCoreRoot
  where
    go ::
      SplitCorePtr ->
      Maybe (CoreF (Maybe ConstructorPattern) PartialCore)
    go ptr = do
      this <- Map.lookup ptr _splitCoreDescendants
      return (bimap pat (PartialCore . go) this)
    pat :: PatternPtr -> Maybe ConstructorPattern
    pat ptr = Map.lookup ptr _splitCorePatterns

split :: PartialCore -> IO SplitCore
split partialCore = do
  root <- newSplitCorePtr
  ((), (childMap, patMap)) <- runWriterT $ go root (unPartialCore partialCore)
  return $ SplitCore root childMap patMap
  where
    go ::
      SplitCorePtr ->
      Maybe (CoreF (Maybe ConstructorPattern) PartialCore) ->
      WriterT (Map SplitCorePtr (CoreF PatternPtr SplitCorePtr),
               Map PatternPtr ConstructorPattern)
        IO
        ()
    go _     Nothing = pure ()
    go place (Just c) = do
      children <- bitraverse pat subtree c
      tell $ (Map.singleton place children, mempty)

    subtree p = do
      here <- liftIO newSplitCorePtr
      go here (unPartialCore p)
      pure here

    pat ::
      Maybe ConstructorPattern ->
      WriterT
        (Map SplitCorePtr (CoreF PatternPtr SplitCorePtr),
         Map PatternPtr ConstructorPattern)
        IO
        PatternPtr
    pat Nothing = liftIO newPatternPtr
    pat (Just it) = do
      here <- liftIO newPatternPtr
      tell (mempty, Map.singleton here it)
      return here
