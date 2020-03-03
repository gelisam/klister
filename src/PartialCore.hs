{-# LANGUAGE TemplateHaskell #-}
module PartialCore where

import Control.Lens
import Data.Bitraversable

import Core


newtype PartialCore = PartialCore
  { unPartialCore ::
      Maybe (CoreF (Maybe ConstructorPattern) PartialCore)
  }
  deriving (Eq, Show)
makePrisms ''PartialCore

nonPartial :: Core -> PartialCore
nonPartial =
  PartialCore . Just . bimap Just nonPartial . unCore


runPartialCore :: PartialCore -> Maybe Core
runPartialCore (PartialCore Nothing) = Nothing
runPartialCore (PartialCore (Just c)) = Core <$> bitraverse id runPartialCore c
