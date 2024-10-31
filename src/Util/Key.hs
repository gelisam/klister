-- | Tiny module to wrap operations for IntMaps

module Util.Key
  (HasKey(..)
  ) where

import Numeric.Natural

class HasKey a where
  getKey :: a -> Int
  fromKey :: Int -> a

instance HasKey Int where
  getKey  = id
  fromKey = id

instance HasKey Natural where
  getKey  = fromIntegral
  fromKey = fromIntegral