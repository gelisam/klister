{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module Type where

import Control.Lens
import Control.Monad
import Data.Foldable
import Data.Data (Data)
import Data.Map (Map)
import Numeric.Natural

import Alpha
import Datatype
import ShortShow
import Unique

newtype MetaPtr = MetaPtr Unique
  deriving (Data, Eq, Ord)

newMetaPtr :: IO MetaPtr
newMetaPtr = MetaPtr <$> newUnique

instance Show MetaPtr where
  show (MetaPtr i) = "(MetaPtr " ++ show (hashUnique i) ++ ")"

data TyF t
  = TSyntax
  | TSignal
  | TFun t t
  | TMacro t
  | TType
  | TDatatype Datatype [t]
  | TSchemaVar Natural
  | TMetaVar MetaPtr
  deriving (Data, Eq, Foldable, Functor, Show, Traversable)
makePrisms ''TyF

data VarKind t = NoLink | Link (TyF t)
  deriving (Functor, Show)
makePrisms ''VarKind

newtype BindingLevel = BindingLevel Natural
  deriving (Eq, Ord, Show)
makePrisms ''BindingLevel

data TVar t = TVar
  { _varKind :: !(VarKind t)
  , _varLevel :: !BindingLevel
  }
  deriving (Functor, Show)
makeLenses ''TVar

newtype TypeStore t = TypeStore (Map MetaPtr (TVar t))
  deriving (Functor, Monoid, Semigroup, Show)

type instance Index (TypeStore t) = MetaPtr
type instance IxValue (TypeStore t) = TVar t

instance Ixed (TypeStore t) where
  ix var f (TypeStore env) = TypeStore <$> ix var f env

instance At (TypeStore t) where
  at x f (TypeStore env) = TypeStore <$> at x f env

data Scheme t = Scheme Natural t
  deriving (Data, Eq, Show)
makeLenses ''Scheme

newtype Ty = Ty
  { unTy :: TyF Ty }
  deriving (Data, Eq, Show)
makePrisms ''Ty

instance AlphaEq a => AlphaEq (TyF a) where
  alphaCheck TSyntax TSyntax = pure ()
  alphaCheck TSignal TSignal = pure ()
  alphaCheck (TFun a1 b1) (TFun a2 b2) = do
    alphaCheck a1 a2
    alphaCheck b1 b2
  alphaCheck (TMacro a) (TMacro b) =
    alphaCheck a b
  alphaCheck (TDatatype a args1) (TDatatype b args2) = do
    guard (a == b)
    guard (length args1 == length args2)
    for_ (zip args1 args2) (uncurry alphaCheck)
  alphaCheck (TSchemaVar i) (TSchemaVar j) =
    guard (i == j)
  alphaCheck (TMetaVar α) (TMetaVar β) =
    guard (α == β)
  alphaCheck _ _ = notAlphaEquivalent

instance ShortShow a => ShortShow (TyF a) where
  shortShow t = show (fmap shortShow t)
