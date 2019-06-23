{-# LANGUAGE TemplateHaskell #-}
module Signals where

import Control.Lens


newtype Signal = Signal Int
  deriving (Eq, Ord, Show)
makePrisms ''Signal
