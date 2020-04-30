{-# LANGUAGE TemplateHaskell #-}
module PartialCore where

import Control.Lens
import Data.Bitraversable

import Core


newtype PartialCore = PartialCore
  { unPartialCore ::
      Maybe (CoreF (Maybe TypePattern) (Maybe ConstructorPattern) PartialCore)
  }
  deriving (Eq, Show)
makePrisms ''PartialCore

nonPartial :: Core -> PartialCore
nonPartial =
  PartialCore . Just . mapCoreF Just Just nonPartial . unCore


runPartialCore :: PartialCore -> Maybe Core
runPartialCore (PartialCore Nothing) = Nothing
runPartialCore (PartialCore (Just c)) = Core <$> traverseCoreF id id runPartialCore c
