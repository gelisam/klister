{-# LANGUAGE TemplateHaskell #-}
module PartialCore where

import Control.Lens

import Core

newtype PartialPattern =
  PartialPattern { unPartialPattern :: Maybe (ConstructorPatternF PartialPattern) }
  deriving (Eq, Show)

newtype PartialCore = PartialCore
  { unPartialCore ::
      Maybe (CoreF (Maybe TypePattern) PartialPattern PartialCore)
  }
  deriving (Eq, Show)
makePrisms ''PartialCore

nonPartial :: Core -> PartialCore
nonPartial =
  PartialCore . Just . mapCoreF Just nonPartialPattern nonPartial . unCore
  where
    nonPartialPattern pat = PartialPattern $ Just $ nonPartialPattern <$> unConstructorPattern pat

runPartialCore :: PartialCore -> Maybe Core
runPartialCore (PartialCore Nothing) = Nothing
runPartialCore (PartialCore (Just c)) = Core <$> traverseCoreF id runPartialPattern runPartialCore c

runPartialPattern :: PartialPattern -> Maybe ConstructorPattern
runPartialPattern (PartialPattern Nothing) = Nothing
runPartialPattern (PartialPattern (Just p)) = ConstructorPattern <$> traverse runPartialPattern p
