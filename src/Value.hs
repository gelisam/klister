{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Value where

import Control.Lens
import Data.Text (Text)
import qualified Data.Text as T

import Core
import Datatype
import Env
import ModuleName
import Signals
import Syntax

type VEnv = Env Var Value
type TEnv = Env MacroVar Value

data MacroAction
  = MacroActionPure Value
  | MacroActionBind MacroAction Closure
  | MacroActionSyntaxError (SyntaxError Syntax)
  | MacroActionSendSignal Signal
  | MacroActionWaitSignal Signal
  | MacroActionIdentEq HowEq Value Value
  | MacroActionLog Syntax
  | MacroActionIntroducer

instance Show MacroAction where
  show _ = "MacroAction..."

data Value
  = ValueClosure Closure
  | ValueSyntax Syntax
  | ValueMacroAction MacroAction
  | ValueSignal Signal
  | ValueCtor Constructor [Value]

instance Show Value where
  show _ = "Value..."

primitiveCtor :: Text -> [Value] -> Value
primitiveCtor name args =
  let ctor = Constructor (KernelName kernelName) (ConstructorName name)
  in ValueCtor ctor args

valueText :: Value -> Text
valueText (ValueClosure _) = "#<closure>"
valueText (ValueSyntax stx) = "'" <> syntaxText stx
valueText (ValueMacroAction _) = "#<macro>"
valueText (ValueSignal s) = "#!" <> T.pack (show s)
valueText (ValueCtor c args) =
  "(" <> view (constructorName . constructorNameText) c <> " " <>
  T.intercalate " " (map valueText args) <> ")"

-- | Find a simple description that is suitable for inclusion in error messages.
describeVal :: Value -> Text
describeVal (ValueClosure _) = "function"
describeVal (ValueSyntax _) = "syntax"
describeVal (ValueMacroAction _) = "macro action"
describeVal (ValueSignal _) = "signal"
describeVal (ValueCtor c _args) =
  view (constructorName . constructorNameText) c

data FOClosure = FOClosure
  { _closureEnv   :: VEnv
  , _closureIdent :: Ident
  , _closureVar   :: Var
  , _closureBody  :: Core
  }

data Closure = FO FOClosure | HO (Value -> Value)

instance Show Closure where
  show _ = "Closure {...}"

makePrisms ''MacroAction
makePrisms ''Value
makeLenses ''Closure
