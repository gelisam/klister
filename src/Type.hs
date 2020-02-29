{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module Type where

import Control.Lens
import Data.Map (Map)
import Data.Unique
import Numeric.Natural

import Datatype

newtype MetaPtr = MetaPtr Unique deriving (Eq, Ord)

newMetaPtr :: IO MetaPtr
newMetaPtr = MetaPtr <$> newUnique

instance Show MetaPtr where
  show (MetaPtr i) = "(MetaPtr " ++ show (hashUnique i) ++ ")"

data TyF t
  = TUnit
  | TBool
  | TSyntax
  | TSignal
  | TFun t t
  | TMacro t
  | TDatatype Datatype [t]
  | TSchemaVar Natural
  | TMetaVar MetaPtr
  deriving (Eq, Foldable, Functor, Show, Traversable)
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

data Scheme t = Scheme Natural t deriving (Eq, Show)
makeLenses ''Scheme

newtype Ty = Ty
  { unTy :: TyF Ty }
  deriving (Eq, Show)
makePrisms ''Ty
