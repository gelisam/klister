{-# LANGUAGE TemplateHaskell #-}
module Syntax.Lexical where

import Control.Lens

import Syntax


data Located a = Located
  { _locatedSrcLoc :: !SrcLoc
  , _locatedValue  :: a
  }
makeLenses ''Located
