{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Expander.Task where

import qualified Data.Text as T

import Binding
import Core
import Datatype
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
  = ExprDest Ty SplitCorePtr
  | TypeDest SplitTypePtr
  | DeclTreeDest DeclTreePtr Scope DeclValidityPtr
  | PatternDest Ty Ty PatternPtr
    -- ^ expression type, scrutinee type, destination pointer
  deriving Show


data ExpanderTask
  = ExpandSyntax MacroDest Syntax
  | AwaitingSignal MacroDest Signal [Closure]
  | AwaitingMacro MacroDest TaskAwaitMacro
  | AwaitingDefn Var Ident Binding SplitCorePtr Ty SplitCorePtr Syntax
    -- ^ Waiting on var, binding, and definiens, destination, syntax to expand
  | AwaitingType SplitTypePtr [AfterTypeTask]
  | ExpandDeclTree DeclTreePtr Scope Syntax DeclValidityPtr
    -- ^ The tree node to fill, the scope, the decls, and the output environment.
  | ExpandDependentDeclTree DeclTreePtr Syntax DeclValidityPtr
    -- ^ The tree node to fill, the decls, and the input environment.
  | InterpretMacroAction MacroDest MacroAction [Closure]
  | ContinueMacroAction MacroDest Value [Closure]
  | EvalDefnAction Var Ident Phase SplitCorePtr
  | GeneralizeType SplitCorePtr Ty SchemePtr
    -- ^ The expression whose type should be generalized, and the place to put the resulting scheme
  | ExpandVar Ty SplitCorePtr Syntax Var
    -- ^ Expected type, destination, origin syntax, and variable to use if it's acceptable
  | EstablishConstructors Scope DeclValidityPtr Datatype [(Ident, Constructor, [SplitTypePtr])]
  | AwaitingPattern PatternPtr Ty SplitCorePtr Syntax
  deriving (Show)

data AfterTypeTask
  = TypeThenUnify SplitCorePtr Ty
  | TypeThenExpandExpr SplitCorePtr Syntax
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
  shortShow (AwaitingDefn _x n _b _defn _t _dest stx) =
    "(AwaitingDefn " ++ shortShow n ++ " " ++ shortShow stx ++ ")"
  shortShow (AwaitingMacro dest t) = "(AwaitingMacro " ++ show dest ++ " " ++ shortShow t ++ ")"
  shortShow (AwaitingType tdest tasks) = "(AwaitingType " ++ show tdest ++ " " ++ show tasks ++ ")"
  shortShow (ExpandDeclTree _dest _sc stx ptr) = "(ExpandDeclTree " ++ T.unpack (syntaxText stx) ++ " " ++ show ptr ++ ")"
  shortShow (ExpandDependentDeclTree _dest stx ptr) = "(ExpandDependentDeclTree " ++ T.unpack (syntaxText stx) ++ " " ++ show ptr ++ ")"
  shortShow (InterpretMacroAction _dest act kont) = "(InterpretMacroAction " ++ show act ++ " " ++ show kont ++ ")"
  shortShow (ContinueMacroAction _dest value kont) = "(ContinueMacroAction " ++ show value ++ " " ++ show kont ++ ")"
  shortShow (EvalDefnAction var name phase _expr) = "(EvalDefnAction " ++ show var ++ " " ++ shortShow name ++ " " ++ show phase ++ ")"
  shortShow (GeneralizeType e _ _) = "(GeneralizeType " ++ show e ++ " _ _)"
  shortShow (ExpandVar t d x v) = "(ExpandVar " ++ show t ++ " " ++ show d ++ " " ++ show x ++ " " ++ show v ++ ")"
  shortShow (EstablishConstructors _ _ dt _) = "(EstablishConstructors " ++ show dt ++ ")"
  shortShow (AwaitingPattern _ _ _ _) = "(AwaitingPattern _ _ _ _)"

instance Pretty VarInfo ExpanderTask where
  pp _ task = string (shortShow task)
