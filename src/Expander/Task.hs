{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Expander.Task where

import Binding
import Core
import Datatype
import Expander.DeclScope
import Kind
import Module
import Phase
import Pretty
import ScopeSet
import SplitCore
import SplitType
import Syntax
import Syntax.SrcLoc
import Type
import Value

-- | One constructor for each 'SyntacticCategory'
data MacroDest
  = ModuleDest DeclTreePtr
    -- ^ produced declaration tree
  | DeclTreeDest DeclTreePtr DeclOutputScopesPtr
    -- ^ produced declaration tree, scopes introduced
  | TypeDest Kind SplitTypePtr
  | ExprDest Ty SplitCorePtr
  | PatternDest Ty PatternPtr
    -- ^ scrutinee type, destination pointer
  | TypePatternDest TypePatternPtr
    -- ^ destination pointer
  deriving Show


data ExpanderTask
  = ExpandSyntax MacroDest Syntax
  | AwaitingTypeCase SrcLoc MacroDest Ty VEnv [(TypePattern, Core)] [Closure]
  | AwaitingMacro MacroDest TaskAwaitMacro
  | AwaitingDefn Var Ident Binding SplitCorePtr Ty SplitCorePtr Syntax
    -- ^ Waiting on var, binding, and definiens, destination, syntax to expand
  | AwaitingType SplitTypePtr [AfterTypeTask]
  | ExpandDeclForms DeclTreePtr ScopeSet DeclOutputScopesPtr DeclOutputScopesPtr Syntax
    -- ^ The produced declaration tree, some already-introduced scopes which
    -- the syntax can already see, some to-be-introduced scopes which the will
    -- see, a destination for all the introduced scopes, including those by the
    -- Syntax's remaining declaration forms.
  | InterpretMacroAction MacroDest MacroAction [Closure]
  | ContinueMacroAction MacroDest Value [Closure]
  | EvalDefnAction Var Ident Phase SplitCorePtr
  | GeneralizeType SplitCorePtr Ty SchemePtr
    -- ^ The expression whose type should be generalized, and the place to put the resulting scheme
  | ExpandVar Ty SplitCorePtr Syntax Var
    -- ^ Expected type, destination, origin syntax, and variable to use if it's acceptable
  | EstablishConstructors ScopeSet DeclOutputScopesPtr Datatype [(Ident, Constructor, [SplitTypePtr])]
  | AwaitingPattern PatternPtr Ty SplitCorePtr Syntax
  | AwaitingTypePattern TypePatternPtr Ty SplitCorePtr Syntax
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


instance Pretty VarInfo ExpanderTask where
  pp _ task = pure $ string (show task)
