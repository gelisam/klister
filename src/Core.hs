module Core where

import Data.Unique

import Syntax


data SyntaxError = SyntaxError
  { syntaxErrorLocations :: [Syntax]
  , syntaxErrorMessage   :: Syntax
  }

type Var = Unique

data CoreF core
  = CoreVar Var
  | CoreLam Ident Var core
  | CoreApp core core
  | CoreSyntaxError SyntaxError
  | CoreSyntax Syntax
  | CoreCase core [(Pattern, core)]
  | CoreIdentifier Ident
  | CoreIdent (ScopedIdent core)
  | CoreEmpty (ScopedEmpty core)
  | CoreCons (ScopedCons core)
  | CoreVec (ScopedVec core)

newtype Core = Core
  { unCore :: CoreF Core }

data Pattern
  = PatternIdentifier Ident Var
  | PatternEmpty
  | PatternCons Ident Var Ident Var
  | PatternVec [(Ident, Var)]

data ScopedIdent core = ScopedIdent
  { scopedIdentIdentifier :: core
  , scopedIdentScope      :: core
  }

data ScopedEmpty core = ScopedEmpty
  { scopedEmptyScope :: core
  }

data ScopedCons core = ScopedCons
  { scopedConsHead  :: core
  , scopedConsTail  :: core
  , scopedConsScope :: core
  }

data ScopedVec core = ScopedVec
  { scopedVecElements :: [core]
  , scopedVecScope    :: core
  }
