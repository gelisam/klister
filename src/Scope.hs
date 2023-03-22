{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE CPP                #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Scope where

import Data.Data (Data)
import Control.Lens

#ifdef KDEBUG
import Data.Text (Text)
#else
import Util.Key
#endif


-- Int should be enough for now - consider bumping to something like int64
#ifndef KDEBUG
newtype Scope = Scope { scopeNum :: Int}
  deriving newtype (Eq, Ord, Show, HasKey)
  deriving stock Data
#else
-- For a debug build Scope keeps a blob of text for debugging the expander
-- output. This will have an impact of the performance of the interpreter so it
-- won't be useful for performance issues
data Scope = Scope { scopeNum :: Int, scopePurpose :: Text }
  deriving (Data, Eq, Ord, Show)
#endif
makeLenses ''Scope
