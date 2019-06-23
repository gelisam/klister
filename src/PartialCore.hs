{-# LANGUAGE TemplateHaskell #-}
module PartialCore where

import Control.Lens

import Core


newtype PartialCore = PartialCore
  { unPartialCore :: Maybe (CoreF PartialCore) }
  deriving (Eq, Show)
makePrisms ''PartialCore

nonPartial :: Core -> PartialCore
nonPartial = PartialCore . Just . fmap nonPartial . unCore


runPartialCore :: PartialCore -> Maybe Core
runPartialCore (PartialCore Nothing) = Nothing
runPartialCore (PartialCore (Just c)) =
  traverse runPartialCore c >>= pure . Core
