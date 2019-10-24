{-# LANGUAGE TemplateHaskell #-}
module Scope where

import Control.Lens

import Data.Text (Text)

-- Int should be enough for now - consider bumping to something like int64
data Scope = Scope { scopeNum :: Int, scopePurpose :: Text }
  deriving (Eq, Ord, Show)
makeLenses ''Scope

