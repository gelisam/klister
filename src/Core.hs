{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, TemplateHaskell #-}
module Core where

import Control.Lens
import Data.Unique

import Alpha
import Signals
import Syntax


data SyntaxError a = SyntaxError
  { _syntaxErrorLocations :: [a]
  , _syntaxErrorMessage   :: a
  }
  deriving (Eq, Functor, Foldable, Show, Traversable)
makeLenses ''SyntaxError

newtype Var = Var Unique
  deriving (AlphaEq, Eq, Ord)

instance Show Var where
  show (Var i) = show (hashUnique i)

data Pattern
  = PatternIdentifier Ident Var
  | PatternEmpty
  | PatternCons Ident Var Ident Var
  | PatternVec [(Ident, Var)]
  deriving (Eq, Show)
makePrisms ''Pattern

data ScopedIdent core = ScopedIdent
  { _scopedIdentIdentifier :: core
  , _scopedIdentScope      :: core
  }
  deriving (Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedIdent

data ScopedEmpty core = ScopedEmpty
  { _scopedEmptyScope :: core
  }
  deriving (Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedEmpty

data ScopedCons core = ScopedCons
  { _scopedConsHead  :: core
  , _scopedConsTail  :: core
  , _scopedConsScope :: core
  }
  deriving (Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedCons

data ScopedVec core = ScopedVec
  { _scopedVecElements :: [core]
  , _scopedVecScope    :: core
  }
  deriving (Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedVec

data CoreF core
  = CoreVar Var
  | CoreLam Ident Var core
  | CoreApp core core
  | CorePure core                       -- :: a -> Macro a
  | CoreBind core core                  -- :: Macro a -> (a -> Macro b) -> Macro b
  | CoreSyntaxError (SyntaxError core)  -- :: Macro a
  | CoreSendSignal Signal               -- :: Macro ()
  | CoreSyntax Syntax
  | CoreCase core [(Pattern, core)]
  | CoreIdentifier Ident
  | CoreIdent (ScopedIdent core)
  | CoreEmpty (ScopedEmpty core)
  | CoreCons (ScopedCons core)
  | CoreVec (ScopedVec core)
  deriving (Eq, Functor, Foldable, Show, Traversable)
makePrisms ''CoreF

newtype Core = Core
  { unCore :: CoreF Core }
  deriving (Eq)
makePrisms ''Core

instance AlphaEq a => AlphaEq (SyntaxError a) where
  alphaCheck (SyntaxError locations1 message1)
             (SyntaxError locations2 message2) = do
    alphaCheck locations1 locations2
    alphaCheck message1   message2

instance AlphaEq core => AlphaEq (CoreF core) where
  alphaCheck (CoreVar var1)
             (CoreVar var2) = do
    alphaCheck var1 var2
  alphaCheck (CoreLam ident1 var1 body1)
             (CoreLam ident2 var2 body2) = do
    alphaCheck ident1 ident2
    alphaCheck var1   var2
    alphaCheck body1  body2
  alphaCheck (CoreApp fun1 arg1)
             (CoreApp fun2 arg2) = do
    alphaCheck fun1 fun2
    alphaCheck arg1 arg2
  alphaCheck (CoreSyntaxError syntaxError1)
             (CoreSyntaxError syntaxError2) = do
    alphaCheck syntaxError1 syntaxError2
  alphaCheck (CoreSyntax syntax1)
             (CoreSyntax syntax2) = do
    alphaCheck syntax1 syntax2
  alphaCheck (CoreCase scrutinee1 cases1)
             (CoreCase scrutinee2 cases2) = do
    alphaCheck scrutinee1 scrutinee2
    alphaCheck cases1 cases2
  alphaCheck (CoreIdentifier stx1)
             (CoreIdentifier stx2) = do
    alphaCheck stx1 stx2
  alphaCheck (CoreIdent scopedIdent1)
             (CoreIdent scopedIdent2) = do
    alphaCheck scopedIdent1 scopedIdent2
  alphaCheck (CoreEmpty scopedEmpty1)
             (CoreEmpty scopedEmpty2) = do
    alphaCheck scopedEmpty1 scopedEmpty2
  alphaCheck (CoreCons scopedCons1)
             (CoreCons scopedCons2) = do
    alphaCheck scopedCons1 scopedCons2
  alphaCheck (CoreVec scopedVec1)
             (CoreVec scopedVec2) = do
    alphaCheck scopedVec1 scopedVec2
  alphaCheck _ _ = notAlphaEquivalent

instance AlphaEq Core where
  alphaCheck (Core x1)
             (Core x2) = do
    alphaCheck x1 x2

instance AlphaEq Pattern where
  alphaCheck (PatternIdentifier n1 x1)
             (PatternIdentifier n2 x2) = do
    alphaCheck n1 n2
    alphaCheck x1 x2
  alphaCheck PatternEmpty
             PatternEmpty = do
    pure ()
  alphaCheck (PatternCons nx1 x1 nxs1 xs1)
             (PatternCons nx2 x2 nxs2 xs2) = do
    alphaCheck nx1  nx2
    alphaCheck x1   x2
    alphaCheck nxs1 nxs2
    alphaCheck xs1  xs2
  alphaCheck (PatternVec xs1)
             (PatternVec xs2) = do
    alphaCheck xs1 xs2
  alphaCheck _ _ = notAlphaEquivalent

instance AlphaEq core => AlphaEq (ScopedIdent core) where
  alphaCheck (ScopedIdent ident1 scope1)
             (ScopedIdent ident2 scope2) = do
    alphaCheck ident1 ident2
    alphaCheck scope1 scope2

instance AlphaEq core => AlphaEq (ScopedEmpty core) where
  alphaCheck (ScopedEmpty scope1)
             (ScopedEmpty scope2) = do
    alphaCheck scope1 scope2

instance AlphaEq core => AlphaEq (ScopedCons core) where
  alphaCheck (ScopedCons hd1 tl1 scope1)
             (ScopedCons hd2 tl2 scope2) = do
    alphaCheck hd1    hd2
    alphaCheck tl1    tl2
    alphaCheck scope1 scope2

instance AlphaEq core => AlphaEq (ScopedVec core) where
  alphaCheck (ScopedVec elements1 scope1)
             (ScopedVec elements2 scope2) = do
    alphaCheck elements1 elements2
    alphaCheck scope1    scope2
