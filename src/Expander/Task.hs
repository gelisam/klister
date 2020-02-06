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
import SplitType
import Syntax
import Type
import Value

data MacroDest
  = ExprDest SplitCorePtr
  | TypeDest SplitTypePtr
  | DeclDest DeclPtr Scope DeclValidityPtr
  deriving Show

data TypeSpec
  = CompleteType Ty
  | IncompleteType SplitTypePtr
  deriving Show

data ExpanderTask
  = ExpandSyntax MacroDest Syntax
  | AwaitingSignal MacroDest Signal [Closure]
  | AwaitingMacro MacroDest TaskAwaitMacro
  | AwaitingMacroType MacroDest TaskAwaitMacroType
  | AwaitingDefn Var Ident Binding SplitCorePtr SplitCorePtr Syntax
    -- ^ Waiting on var, binding, and definiens, destination, syntax to expand
  | ExpandDecl DeclPtr Scope Syntax DeclValidityPtr
    -- ^ Where to put it, the scope, the decl, where to put the phase
  | ExpandMoreDecls ModBodyPtr Scope Syntax DeclValidityPtr
    -- Depends on the binding of the name(s) from the decl and the phase
  | InterpretMacroAction MacroDest MacroAction [Closure]
  | ContinueMacroAction MacroDest Value [Closure]
  | EvalDefnAction Var Ident Phase SplitCorePtr
  | TypeCheck SplitCorePtr TypeSpec
  | TypeCheckDecl DeclPtr
  | GeneralizeType SplitCorePtr Ty SchemePtr
    -- ^ The expression whose type should be generalized, and the place to put the resulting scheme
  | TypeCheckVar SplitCorePtr Ty
    -- ^ The variable expression and the expected type
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

data TaskAwaitMacroType = TaskAwaitMacroType
  { awaitMacroTypeBinding :: Binding
  , awaitMacroTypeName :: MacroVar
  , awaitMacroTypeIdent :: Ident
  , awaitMacroTypeLocation :: SplitCorePtr -- the destination into which the macro was expanded.
  , awaitMacroTypeSyntax :: Syntax -- the syntax object to be expanded once the macro is available
  }
  deriving (Show)


instance ShortShow TaskAwaitMacro where
  shortShow (TaskAwaitMacro _ _ x deps _ stx) =
    "(TaskAwaitMacro " ++ show x ++ " " ++ show deps ++ " " ++ T.unpack (pretty stx) ++ ")"

instance ShortShow TaskAwaitMacroType where
  shortShow = show

instance ShortShow ExpanderTask where
  shortShow (ExpandSyntax _dest stx) = "(ExpandSyntax " ++ T.unpack (pretty stx) ++ ")"
  shortShow (AwaitingSignal _dest on _k) = "(AwaitingSignal " ++ show on ++ ")"
  shortShow (AwaitingDefn _x n _b _defn _dest stx) =
    "(AwaitingDefn " ++ shortShow n ++ " " ++ shortShow stx ++ ")"
  shortShow (AwaitingMacro dest t) = "(AwaitingMacro " ++ show dest ++ " " ++ shortShow t ++ ")"
  shortShow (AwaitingMacroType dest t) = "(AwaitingMacro " ++ show dest ++ " " ++ shortShow t ++ ")"
  shortShow (ExpandDecl _dest _sc stx ptr) = "(ExpandDecl " ++ T.unpack (syntaxText stx) ++ " " ++ show ptr ++ ")"
  shortShow (ExpandMoreDecls _dest _sc stx ptr) = "(ExpandMoreDecls " ++ T.unpack (syntaxText stx) ++ " " ++ show ptr ++ ")"
  shortShow (InterpretMacroAction _dest act kont) = "(InterpretMacroAction " ++ show act ++ " " ++ show kont ++ ")"
  shortShow (ContinueMacroAction _dest value kont) = "(ContinueMacroAction " ++ show value ++ " " ++ show kont ++ ")"
  shortShow (EvalDefnAction var name phase _expr) = "(EvalDefnAction " ++ show var ++ " " ++ shortShow name ++ " " ++ show phase ++ ")"
  shortShow (TypeCheck _ _) = "(TypeCheck _ _)"
  shortShow (TypeCheckDecl _) = "(TypeCheckDecl _ )"
  shortShow (GeneralizeType _ _ _) = "(GeneralizeType _ _ _)"
  shortShow (TypeCheckVar _ t) = "(TypeCheckVar _ " ++ show t ++ ")"

instance Pretty VarInfo ExpanderTask where
  pp _ task = string (shortShow task)
