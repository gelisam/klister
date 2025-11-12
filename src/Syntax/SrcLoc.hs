{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
module Syntax.SrcLoc where

import Control.Monad
import Control.Lens
import Data.Data (Data)

import Alpha

data SrcPos = SrcPos
  { _srcPosLine :: !Int
  , _srcPosCol  :: !Int
  }
  deriving (Data, Eq, Show)
makeLenses ''SrcPos

data SrcLoc = SrcLoc
  { _srcLocFilePath :: !FilePath
  , _srcLocStart    :: !SrcPos
  , _srcLocEnd      :: !SrcPos
  }
  deriving (Data, Eq, Show)
makeLenses ''SrcLoc

instance AlphaEq SrcLoc where
  alphaCheck x y = guard (x == y)
