module PartialCore where

import Core


newtype PartialCore = PartialCore
  { unPartialCore :: Maybe (CoreF PartialCore) }

nonPartial :: Core -> PartialCore
nonPartial = PartialCore . Just . fmap nonPartial . unCore


runPartialCore :: PartialCore -> Maybe Core
runPartialCore (PartialCore Nothing) = Nothing
runPartialCore (PartialCore (Just c)) =
  traverse runPartialCore c >>= pure . Core
