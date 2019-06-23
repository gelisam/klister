{-# LANGUAGE TemplateHaskell #-}
module Value where

import Control.Lens
import Data.Map
import Data.Unique

import Signals
import Syntax
import Core


type Env = Map Unique (Ident, Value)

data MacroAction
  = MacroActionPure Value
  | MacroActionBind MacroAction Closure
  | MacroActionSyntaxError (SyntaxError Syntax)
  | MacroActionSendSignal Signal

data Value
  = ValueClosure Closure
  | ValueSyntax Syntax
  | ValueMacroAction MacroAction

data Closure = Closure
  { _closureEnv   :: Env
  , _closureIdent :: Ident
  , _closureVar   :: Var 
  , _closureBody  :: Core
  }

makePrisms ''MacroAction
makePrisms ''Value
makeLenses ''Closure
