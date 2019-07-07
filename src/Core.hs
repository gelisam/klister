{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
module Core where

import Control.Lens hiding (elements)
import Control.Monad
import Data.Unique

import Alpha
import ShortShow
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
  | CoreSendSignal core                 -- :: Macro ()
  | CoreSyntax Syntax
  | CoreCase core [(Pattern, core)]
  | CoreIdentifier Ident
  | CoreSignal Signal
  | CoreIdent (ScopedIdent core)
  | CoreEmpty (ScopedEmpty core)
  | CoreCons (ScopedCons core)
  | CoreVec (ScopedVec core)
  deriving (Eq, Functor, Foldable, Show, Traversable)
makePrisms ''CoreF

newtype Core = Core
  { unCore :: CoreF Core }
  deriving (Eq, Show)
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
  alphaCheck (CoreLam _ var1 body1)
             (CoreLam _ var2 body2) = do
    alphaCheck var1   var2
    alphaCheck body1  body2
  alphaCheck (CoreApp fun1 arg1)
             (CoreApp fun2 arg2) = do
    alphaCheck fun1 fun2
    alphaCheck arg1 arg2
  alphaCheck (CorePure x1)
             (CorePure x2) = do
    alphaCheck x1 x2
  alphaCheck (CoreBind hd1 tl1)
             (CoreBind hd2 tl2) = do
    alphaCheck hd1 hd2
    alphaCheck tl1 tl2
  alphaCheck (CoreSyntaxError syntaxError1)
             (CoreSyntaxError syntaxError2) = do
    alphaCheck syntaxError1 syntaxError2
    alphaCheck syntaxError1 syntaxError2
  alphaCheck (CoreSendSignal signal1)
             (CoreSendSignal signal2) = do
    alphaCheck signal1 signal2
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
  alphaCheck (CoreSignal s1)
             (CoreSignal s2) =
    guard $ s1 == s2
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
  alphaCheck (PatternIdentifier _ x1)
             (PatternIdentifier _ x2) = do
    alphaCheck x1 x2
  alphaCheck PatternEmpty
             PatternEmpty = do
    pure ()
  alphaCheck (PatternCons _ x1 _ xs1)
             (PatternCons _ x2 _ xs2) = do
    alphaCheck x1   x2
    alphaCheck xs1  xs2
  alphaCheck (PatternVec xs1)
             (PatternVec xs2) = do
    alphaCheck (map snd xs1) (map snd xs2)
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


instance ShortShow a => ShortShow (SyntaxError a) where
  shortShow (SyntaxError locations message)
    = "(SyntaxError "
   ++ shortShow locations
   ++ " "
   ++ shortShow message
   ++ ")"

instance ShortShow Var where
  shortShow (Var x) = shortShow x

instance ShortShow core => ShortShow (CoreF core) where
  shortShow (CoreVar var)
    = "(Var "
   ++ shortShow var
   ++ ")"
  shortShow (CoreLam _ x body)
    = "(Lam "
   ++ shortShow x
   ++ " "
   ++ shortShow body
   ++ ")"
  shortShow (CoreApp fun arg)
    = "(App "
   ++ shortShow fun
   ++ " "
   ++ shortShow arg
   ++ ")"
  shortShow (CorePure x)
    = "(Pure "
   ++ shortShow x
   ++ ")"
  shortShow (CoreBind hd tl)
    = "(Bind "
   ++ shortShow hd
   ++ " "
   ++ shortShow tl
   ++ ")"
  shortShow (CoreSyntaxError syntaxError)
    = "(SyntaxError "
   ++ shortShow syntaxError
   ++ ")"
  shortShow (CoreSendSignal signal)
    = "(SendSignal "
   ++ shortShow signal
   ++ ")"
  shortShow (CoreSyntax syntax)
    = "(Syntax "
   ++ shortShow syntax
   ++ ")"
  shortShow (CoreCase scrutinee cases)
    = "(Case "
   ++ shortShow scrutinee
   ++ " "
   ++ shortShow cases
   ++ ")"
  shortShow (CoreIdentifier stx)
    = "(Identifier "
   ++ shortShow stx
   ++ ")"
  shortShow (CoreSignal signal)
    = shortShow signal
  shortShow (CoreIdent scopedIdent)
    = "(Ident "
   ++ shortShow scopedIdent
   ++ ")"
  shortShow (CoreEmpty scopedEmpty)
    = "(Empty "
   ++ shortShow scopedEmpty
   ++ ")"
  shortShow (CoreCons scopedCons)
    = "(Cons "
   ++ shortShow scopedCons
   ++ ")"
  shortShow (CoreVec scopedVec)
    = "(Vec "
   ++ shortShow scopedVec
   ++ ")"

instance ShortShow Core where
  shortShow (Core x) = shortShow x

instance ShortShow Pattern where
  shortShow (PatternIdentifier _ x) = shortShow x
  shortShow PatternEmpty = "Empty"
  shortShow (PatternCons _ x _ xs)
    = "(Cons "
   ++ shortShow x
   ++ " "
   ++ shortShow xs
   ++ ")"
  shortShow (PatternVec xs)
    = "(Vec "
   ++ shortShow (map snd xs)
   ++ ")"

instance ShortShow core => ShortShow (ScopedIdent core) where
  shortShow (ScopedIdent ident scope)
    = "(ScopedIdent "
   ++ shortShow ident
   ++ " "
   ++ shortShow scope
   ++ ")"

instance ShortShow core => ShortShow (ScopedEmpty core) where
  shortShow (ScopedEmpty scope)
    = "(ScopedEmpty "
   ++ shortShow scope
   ++ ")"

instance ShortShow core => ShortShow (ScopedCons core) where
  shortShow (ScopedCons hd tl scope)
    = "(ScopedCons "
   ++ shortShow hd
   ++ " "
   ++ shortShow tl
   ++ " "
   ++ shortShow scope
   ++ ")"

instance ShortShow core => ShortShow (ScopedVec core) where
  shortShow (ScopedVec elements scope)
    = "(ScopedVec "
   ++ shortShow elements
   ++ " "
   ++ shortShow scope
   ++ ")"
