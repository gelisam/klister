{-# LANGUAGE TemplateHaskell #-}
module Syntax.SrcLoc where

import Control.Monad
import Control.Lens

import Alpha
import ShortShow

data SrcPos = SrcPos
  { _srcPosLine :: !Int
  , _srcPosCol  :: !Int
  }
  deriving (Eq, Show)
makeLenses ''SrcPos

instance ShortShow SrcPos where
  shortShow (SrcPos l c) = show l ++ "." ++ show c

data SrcLoc = SrcLoc
  { _srcLocFilePath :: !FilePath
  , _srcLocStart    :: !SrcPos
  , _srcLocEnd      :: !SrcPos
  }
  deriving (Eq, Show)
makeLenses ''SrcLoc

instance AlphaEq SrcLoc where
  alphaCheck x y = guard (x == y)

instance ShortShow SrcLoc where
  shortShow (SrcLoc fn beg end) =
    reverse (take 10 (reverse fn)) ++ ":" ++
    shortShow beg ++ "-" ++
    shortShow end
