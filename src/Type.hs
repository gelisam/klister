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
import Data.Map (Map)
import Data.Unique
import Numeric.Natural

import Alpha
import Datatype
import ShortShow

newtype MetaPtr = MetaPtr Unique deriving (Eq, Ord)

newMetaPtr :: IO MetaPtr
newMetaPtr = MetaPtr <$> newUnique

instance Show MetaPtr where
  show (MetaPtr i) = "(MetaPtr " ++ show (hashUnique i) ++ ")"

data TypeConstructor
  = TSyntax
  | TSignal
  | TString
  | TFun
  | TMacro
  | TType
  | TDatatype Datatype
  | TSchemaVar Natural
  | TMetaVar MetaPtr
  deriving (Eq, Show)
makePrisms ''TypeConstructor

data TyF t = TyF
  { outermostCtor :: TypeConstructor
  , typeArgs      :: [t]
  }
  deriving (Eq, Foldable, Functor, Show, Traversable)
makeLenses ''TyF

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

tSyntax :: Ty
tSyntax = Ty $ TyF TSyntax []

tSignal :: Ty
tSignal = Ty $ TyF TSignal []

tString :: Ty
tString = Ty $ TyF TString []

tFun :: Ty -> Ty -> Ty
tFun t1 t2 = Ty $ TyF TFun [t1, t2]
infixr 9 `tFun`

tMacro :: Ty -> Ty
tMacro t = Ty $ TyF TMacro [t]

tType :: Ty
tType = Ty $ TyF TType []

tDatatype :: Datatype -> [Ty] -> Ty
tDatatype x ts = Ty $ TyF (TDatatype x) ts

tSchemaVar :: Natural -> Ty
tSchemaVar x = Ty $ TyF (TSchemaVar x) []

tMetaVar :: MetaPtr -> Ty
tMetaVar x = Ty $ TyF (TMetaVar x) []

instance AlphaEq a => AlphaEq (TyF a) where
  alphaCheck (TyF ctor1 args1) (TyF ctor2 args2) = do
    guard (ctor1 == ctor2)
    guard (length args1 == length args2)
    for_ (zip args1 args2) (uncurry alphaCheck)

instance ShortShow a => ShortShow (TyF a) where
  shortShow t = show (fmap shortShow t)
