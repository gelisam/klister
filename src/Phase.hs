{-# LANGUAGE TemplateHaskell #-}

module Phase (Phase, runtime, prior) where

import Control.Lens
import Numeric.Natural

newtype Phase = Phase Natural
  deriving (Eq, Ord, Show)
makePrisms ''Phase

runtime :: Phase
runtime = Phase 0

prior :: Phase -> Phase
prior (Phase i) = Phase (i + 1)
