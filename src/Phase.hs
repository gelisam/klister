{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Phase (Phase(..), runtime, prior, posterior, Phased(..)) where

import Control.Lens
import Data.Data (Data)
import Data.Sequence (Seq)
import Numeric.Natural

import ShortShow

import Util.Key

newtype Phase = Phase { phaseNum :: Natural }
  deriving newtype (Eq, Ord, Show, Num)
  deriving stock Data
makePrisms ''Phase

instance HasKey Phase where
  getKey (Phase n) = fromInteger $ toInteger n
  fromKey i = Phase $! fromIntegral  i
  {-# INLINE getKey  #-}
  {-# INLINE fromKey #-}

instance ShortShow Phase where
  shortShow (Phase i) = "p" ++ show i

runtime :: Phase
runtime = Phase 0

prior :: Phase -> Phase
prior (Phase i) = Phase (i + 1)

posterior :: Phase -> Phase
posterior (Phase i) = Phase (i - 1)

class Phased a where
  shift :: Natural -> a -> a

instance Phased Phase where
  shift j (Phase i) = Phase (i + j)

instance Phased a => Phased [a] where
  shift i = fmap (shift i)

instance Phased a => Phased (Seq a) where
  shift i = fmap (shift i)
