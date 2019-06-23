{-# LANGUAGE TemplateHaskell #-}
module Value where

import Control.Lens
import Data.Map

import Signals
import Syntax
import Core


type Env = Map Var (Ident, Value)

data MacroAction
  = MacroActionPure Value
  | MacroActionBind MacroAction Closure
  | MacroActionSyntaxError (SyntaxError Syntax)
  | MacroActionSendSignal Signal
  deriving (Eq, Show)

data Value
  = ValueClosure Closure
  | ValueSyntax Syntax
  | ValueMacroAction MacroAction
  deriving (Eq, Show)

data Closure = Closure
  { _closureEnv   :: Env
  , _closureIdent :: Ident
  , _closureVar   :: Var
  , _closureBody  :: Core
  }
  deriving (Eq, Show)

makePrisms ''MacroAction
makePrisms ''Value
makeLenses ''Closure
