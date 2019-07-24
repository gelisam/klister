{-# LANGUAGE TemplateHaskell #-}
module Syntax.Lexical where

import Control.Lens

import Syntax.SrcLoc


data Located a = Located
  { _locatedSrcLoc :: !SrcLoc
  , _locatedValue  :: a
  }
makeLenses ''Located
