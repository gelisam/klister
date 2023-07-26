-- | Tiny module to wrap operations for IntMaps

module Util.Key
  (HasKey(..)
  ) where

class HasKey a where
  getKey :: a -> Int
  fromKey :: Int -> a

instance HasKey Int where
  getKey  = id
  fromKey = id
