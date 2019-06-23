{-# LANGUAGE TemplateHaskell #-}
module Value where

import Control.Lens
import Data.Map
import Data.Unique

import Syntax
import Core


type Env = Map Unique (Ident, Value)

data Value
  = ValueClosure Closure
  | ValueSyntax Syntax

data Closure = Closure
  { _closureEnv   :: Env
  , _closureIdent :: Ident
  , _closureVar   :: Var 
  , _closureBody  :: Core
  }

makePrisms ''Value
makeLenses ''Closure
