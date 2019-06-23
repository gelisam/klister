module Syntax.Lexical where

import Syntax

data Located a
  = Located !SrcLoc a
