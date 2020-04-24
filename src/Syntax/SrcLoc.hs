{-# LANGUAGE TemplateHaskell #-}
module Syntax.SrcLoc where

import Control.Monad
import Control.Lens
import Data.Ord (comparing)

import Alpha
import ShortShow

data SrcPos = SrcPos
  { _srcPosLine :: !Int
  , _srcPosCol  :: !Int
  }
  deriving (Eq, Show)
makeLenses ''SrcPos

-- This is the derived instance, but because it's used in things like
-- error messages rather than just in things like Map keys, we write
-- it explicitly
instance Ord SrcPos where
  compare =
    comparing (view srcPosLine) <>
    comparing (view srcPosCol)

instance ShortShow SrcPos where
  shortShow (SrcPos l c) = show l ++ "." ++ show c

data SrcLoc = SrcLoc
  { _srcLocFilePath :: !FilePath
  , _srcLocStart    :: !SrcPos
  , _srcLocEnd      :: !SrcPos
  }
  deriving (Eq, Show)
makeLenses ''SrcLoc

instance Ord SrcLoc where
  compare loc1 loc2 =
    comparing (view srcLocFilePath) loc1 loc2 <>
    comparing (view srcLocStart) loc1 loc2 <>
    -- NB They are flipped so that shorter (more specific) locations come before others
    comparing (view srcLocEnd) loc2 loc1

instance AlphaEq SrcLoc where
  alphaCheck x y = guard (x == y)

instance ShortShow SrcLoc where
  shortShow (SrcLoc fn beg end) =
    reverse (take 10 (reverse fn)) ++ ":" ++
    shortShow beg ++ "-" ++
    shortShow end
