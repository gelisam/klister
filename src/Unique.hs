{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}
-- | A drop-in replacement for Data.Unique which has a Data instance.
module Unique (Unique, newUnique, hashUnique) where

import Data.Data (Data)
import Data.IORef
import System.IO.Unsafe
import Data.Hashable

import Util.Key


newtype Unique = Unique Int
  deriving newtype (Eq, Ord, Hashable)
  deriving stock Data

uniqSource :: IORef Int
uniqSource = unsafePerformIO (newIORef 0)
{-# NOINLINE uniqSource #-}

-- | Creates a new object of type 'Unique'.  The value returned will
-- not compare equal to any other value of type 'Unique' returned by
-- previous calls to 'newUnique'.  There is no limit on the number of
-- times 'newUnique' may be called.
newUnique :: IO Unique
newUnique = do
  r <- atomicModifyIORef' uniqSource $ \x -> let !z = x+1 in (z,z)
  return (Unique r)

hashUnique :: Unique -> Int
hashUnique (Unique x) = x

instance HasKey Unique where
  getKey u = hashUnique u
  fromKey i = Unique $! i
