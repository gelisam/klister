{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Expander.Task where

import Numeric.Natural
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
  | DeclDest DeclPtr Scope DeclValidityPtr
  deriving Show


data ExpanderTask
  = ExpandSyntax MacroDest Syntax
  | AwaitingSignal MacroDest Signal [Closure]
  | AwaitingMacro MacroDest TaskAwaitMacro
  | AwaitingDefn Var Ident Binding SplitCorePtr Ty SplitCorePtr Syntax
    -- ^ Waiting on var, binding, and definiens, destination, syntax to expand
  | AwaitingType SplitTypePtr [AfterTypeTask]
  | ExpandDecl DeclPtr Scope Syntax DeclValidityPtr
    -- ^ Where to put it, the scope, the decl, where to put the phase
  | ExpandMoreDecls ModBodyPtr Scope Syntax DeclValidityPtr
    -- Depends on the binding of the name(s) from the decl and the phase
  | InterpretMacroAction MacroDest MacroAction [Closure]
  | ContinueMacroAction MacroDest Value [Closure]
  | EvalDefnAction Var Ident Phase SplitCorePtr
  | GeneralizeType SplitCorePtr Ty SchemePtr
    -- ^ The expression whose type should be generalized, and the place to put the resulting scheme
  | ExpandVar Ty SplitCorePtr Syntax Var
    -- ^ Expected type, destination, origin syntax, and variable to use if it's acceptable
  | EstablishConstructors DeclValidityPtr Datatype Natural [(Ident, Constructor, [SplitTypePtr])]


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
  shortShow (ExpandDecl _dest _sc stx ptr) = "(ExpandDecl " ++ T.unpack (syntaxText stx) ++ " " ++ show ptr ++ ")"
  shortShow (ExpandMoreDecls _dest _sc stx ptr) = "(ExpandMoreDecls " ++ T.unpack (syntaxText stx) ++ " " ++ show ptr ++ ")"
  shortShow (InterpretMacroAction _dest act kont) = "(InterpretMacroAction " ++ show act ++ " " ++ show kont ++ ")"
  shortShow (ContinueMacroAction _dest value kont) = "(ContinueMacroAction " ++ show value ++ " " ++ show kont ++ ")"
  shortShow (EvalDefnAction var name phase _expr) = "(EvalDefnAction " ++ show var ++ " " ++ shortShow name ++ " " ++ show phase ++ ")"
  shortShow (GeneralizeType e _ _) = "(GeneralizeType " ++ show e ++ " _ _)"
  shortShow (ExpandVar t d x v) = "(ExpandVar " ++ show t ++ " " ++ show d ++ " " ++ show x ++ " " ++ show v ++ ")"
  shortShow (EstablishConstructors _ dt _ _) = "(EstablishConstructors " ++ show dt ++ ")"

instance Pretty VarInfo ExpanderTask where
  pp _ task = string (shortShow task)
