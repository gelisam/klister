{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
module Scope where

import Data.Data (Data)
import Control.Lens

import Data.Text (Text)

-- Int should be enough for now - consider bumping to something like int64
data Scope = Scope { scopeNum :: Int, scopePurpose :: Text }
  deriving (Data, Eq, Ord, Show)
makeLenses ''Scope

