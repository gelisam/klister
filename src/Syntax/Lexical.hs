module Syntax.Lexical where

import Data.Text (Text)

import Syntax

data Located a
  = Located !SrcLoc a
