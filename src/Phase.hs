{-# LANGUAGE TemplateHaskell #-}

module Phase (Phase, phaseNum, runtime, prior, PhaseSpec(..), Phased(..)) where

import Control.Lens
import Numeric.Natural

newtype Phase = Phase { phaseNum :: Natural }
  deriving (Eq, Ord, Show)
makePrisms ''Phase

data PhaseSpec = AllPhases | SpecificPhase !Phase
makePrisms ''PhaseSpec

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
