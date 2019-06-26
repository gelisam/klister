{-# LANGUAGE TemplateHaskell #-}
module Signals where

import Control.Lens
import Control.Monad

import Alpha


newtype Signal = Signal Int
  deriving (Eq, Ord, Show)
makePrisms ''Signal


instance AlphaEq Signal where
  alphaCheck (Signal x1) (Signal x2) = guard (x1 == x2)
