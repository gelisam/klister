{-# LANGUAGE TemplateHaskell #-}
module Value where

import Control.Lens
import Data.Map

import Syntax
import Core


type Env = Map Var (Ident, Value)

data Value
  = ValueClosure Closure
  | ValueSyntax Syntax
  deriving (Eq)

data Closure = Closure
  { _closureEnv   :: Env
  , _closureIdent :: Ident
  , _closureVar   :: Var
  , _closureBody  :: Core
  }
  deriving (Eq)

makePrisms ''Value
makeLenses ''Closure
