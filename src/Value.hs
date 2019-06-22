module Value where

import Data.Map
import Data.Unique

import Syntax
import Core


type Env = Map Unique (Ident, Value)

data Value
  = ValueClosure Closure
  | ValueSyntax Syntax

data Closure = Closure
  { closureEnv   :: Env
  , closureIdent :: Ident
  , closureVar   :: Var 
  , closureBody  :: Core
  }
