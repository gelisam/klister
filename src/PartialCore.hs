module PartialCore where

import Core


newtype PartialCore = PartialCore
  { unPartialCore :: CoreF (Maybe PartialCore) }

nonPartial :: Core -> PartialCore
nonPartial = PartialCore . fmap go . unCore
  where
    go :: Core -> Maybe PartialCore
    go = Just . nonPartial

runPartialCore :: PartialCore -> Maybe Core
runPartialCore = fmap Core . traverse go . unPartialCore
  where
    go :: Maybe PartialCore -> Maybe Core
    go maybePartialCore = do
      partialCore <- maybePartialCore
      runPartialCore partialCore
