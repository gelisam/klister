{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}

module Phase (Phase, phaseNum, runtime, prior, Phased(..)) where

import Control.Lens
import Data.Data (Data)
import Numeric.Natural

import ShortShow

newtype Phase = Phase { phaseNum :: Natural }
  deriving (Data, Eq, Ord, Show)
makePrisms ''Phase

instance ShortShow Phase where
  shortShow (Phase i) = "p" ++ show i

runtime :: Phase
runtime = Phase 0

prior :: Phase -> Phase
prior (Phase i) = Phase (i + 1)

class Phased a where
  shift :: Natural -> a -> a

instance Phased Phase where
  shift j (Phase i) = Phase (i + j)

instance Phased a => Phased [a] where
  shift i = fmap (shift i)
