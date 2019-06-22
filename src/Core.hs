module Core where

import Data.Unique

import Syntax


type Var = Unique

-- TODO: figure out how this should be defined
data ScopeContext = ScopeContext

data Core
  = CoreVar Var
  | CoreLam Var Core
  | CoreApp Core Core
  | CoreSyntaxError Syntax
  | CoreSyntax Syntax SrcLoc ScopeContext
  | CoreCase [(Pattern, Core)]
  | CoreIdentifier Var
  | CoreIdent ScopedIdent
  | CoreEmpty ScopedEmpty
  | CoreCons ScopedCons
  | CoreVec ScopedVec

data Pattern
  = PatternIdentifier Var
  | PatternEmpty
  | PatternCons Var Var
  | PatternVec [Var]

data ScopedIdent = ScopedIdent
  { scopedIdentIdentifier :: Core
  , scopedIdentScope      :: Core
  }

data ScopedEmpty = ScopedEmpty
  { scopedEmptyScope :: Core
  }

data ScopedCons = ScopedCons
  { scopedConsHead  :: Core
  , scopedConsTail  :: Core
  , scopedConsScope :: Core
  }

data ScopedVec = ScopedVec
  { scopedVecElements :: Core
  , scopedVecScope    :: Core
  }
