module Core where

import Data.Unique

import Syntax


data SyntaxError = SyntaxError
  { syntaxErrorLocations :: [Syntax]
  , syntaxErrorMessage   :: Syntax
  }

type Var = Unique

data Core
  = CoreVar Var
  | CoreLam Ident Var Core
  | CoreApp Core Core
  | CoreSyntaxError SyntaxError
  | CoreSyntax Syntax
  | CoreCase Core [(Pattern, Core)]
  | CoreIdentifier Ident
  | CoreIdent ScopedIdent
  | CoreEmpty ScopedEmpty
  | CoreCons ScopedCons
  | CoreVec ScopedVec

data Pattern
  = PatternIdentifier Ident Var
  | PatternEmpty
  | PatternCons Ident Var Ident Var
  | PatternVec [(Ident, Var)]

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
  { scopedVecElements :: [Core]
  , scopedVecScope    :: Core
  }
