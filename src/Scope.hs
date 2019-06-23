{-# LANGUAGE TemplateHaskell #-}
module Scope where

import Control.Lens


-- Int should be enough for now - consider bumping to something like int64
newtype Scope = Scope Int
  deriving (Eq, Ord, Show)
makePrisms ''Scope

nextScope :: Scope -> Scope
nextScope (Scope i) = Scope (i + 1)
