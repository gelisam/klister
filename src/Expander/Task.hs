{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Expander.Task where

import qualified Data.Text as T

import Binding
import Core
import Expander.DeclScope
import Module
import Phase
import Pretty
import Scope
import ShortShow
import Signals
import SplitCore
import Syntax
import Value

data ExpanderTask
  = ExpandSyntax SplitCorePtr Syntax
  | AwaitingSignal SplitCorePtr Signal [Closure]
  | AwaitingMacro SplitCorePtr TaskAwaitMacro
  | AwaitingDefn Var Ident Binding SplitCorePtr SplitCorePtr Syntax
    -- ^ Waiting on var, binding, and definiens, destination, syntax to expand
  | ExpandDecl DeclPtr Scope Syntax DeclValidityPtr
    -- ^ Where to put it, the scope, the decl, where to put the phase
  | ExpandMoreDecls ModBodyPtr Scope Syntax DeclValidityPtr
    -- Depends on the binding of the name(s) from the decl and the phase
  | InterpretMacroAction SplitCorePtr MacroAction [Closure]
  | ContinueMacroAction SplitCorePtr Value [Closure]
  | EvalDefnAction Var Ident Phase SplitCorePtr
  deriving (Show)

data TaskAwaitMacro = TaskAwaitMacro
  { awaitMacroBinding :: Binding
  , awaitMacroName :: MacroVar
  , awaitMacroIdent :: Ident
  , awaitMacroDependsOn :: [SplitCorePtr] -- the [Unique] is the collection of open problems that represent the macro's expansion. When it's empty, the macro is available.
  , awaitMacroLocation :: SplitCorePtr -- the destination into which the macro will be expanded.
  , awaitMacroSyntax :: Syntax -- the syntax object to be expanded once the macro is available
  }
  deriving (Show)

instance ShortShow TaskAwaitMacro where
  shortShow (TaskAwaitMacro _ _ x deps _ stx) =
    "(TaskAwaitMacro " ++ show x ++ " " ++ show deps ++ " " ++ T.unpack (pretty stx) ++ ")"

instance ShortShow ExpanderTask where
  shortShow (ExpandSyntax _dest stx) = "(ExpandSyntax " ++ T.unpack (pretty stx) ++ ")"
  shortShow (AwaitingSignal _dest on _k) = "(AwaitingSignal " ++ show on ++ ")"
  shortShow (AwaitingDefn _x n _b _defn _dest stx) =
    "(AwaitingDefn " ++ shortShow n ++ " " ++ shortShow stx ++ ")"
  shortShow (AwaitingMacro dest t) = "(AwaitingMacro " ++ show dest ++ " " ++ shortShow t ++ ")"
  shortShow (ExpandDecl _dest _sc stx ptr) = "(ExpandDecl " ++ T.unpack (syntaxText stx) ++ " " ++ show ptr ++ ")"
  shortShow (ExpandMoreDecls _dest _sc stx ptr) = "(ExpandMoreDecls " ++ T.unpack (syntaxText stx) ++ " " ++ show ptr ++ ")"
  shortShow (InterpretMacroAction _dest act kont) = "(InterpretMacroAction " ++ show act ++ " " ++ show kont ++ ")"
  shortShow (ContinueMacroAction _dest value kont) = "(ContinueMacroAction " ++ show value ++ " " ++ show kont ++ ")"
  shortShow (EvalDefnAction var name phase _expr) = "(EvalDefnAction " ++ show var ++ " " ++ shortShow name ++ " " ++ show phase ++ ")"

instance Pretty VarInfo ExpanderTask where
  pp _ task = string (shortShow task)
