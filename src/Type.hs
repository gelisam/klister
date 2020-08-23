{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import Kind
import ShortShow
import Unique

newtype MetaPtr = MetaPtr Unique
  deriving (Data, Eq, Ord)

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
  deriving (Data, Eq, Show)
makePrisms ''TypeConstructor

data TyF t = TyF
  { outermostCtor :: TypeConstructor
  , typeArgs      :: [t]
  }
  deriving (Data, Eq, Foldable, Functor, Show, Traversable)
makeLenses ''TyF

data VarLinkage t = NoLink | Link (TyF t)
  deriving (Functor, Show)
makePrisms ''VarLinkage

newtype BindingLevel = BindingLevel Natural
  deriving (Eq, Ord, Show)
makePrisms ''BindingLevel

data TVar t = TVar
  { _varLinkage :: !(VarLinkage t)
  , _varLevel :: !BindingLevel
  , _varKind :: !Kind
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

data Scheme t = Scheme [Kind] t
  deriving (Data, Eq, Show)
makeLenses ''Scheme

newtype Ty = Ty
  { unTy :: TyF Ty }
  deriving (Data, Eq, Show)
makePrisms ''Ty

instance AlphaEq a => AlphaEq (TyF a) where
  alphaCheck (TyF ctor1 args1) (TyF ctor2 args2) = do
    guard (ctor1 == ctor2)
    guard (length args1 == length args2)
    for_ (zip args1 args2) (uncurry alphaCheck)

instance ShortShow a => ShortShow (TyF a) where
  shortShow t = show (fmap shortShow t)


class TyLike a arg | a -> arg where
  tSyntax    :: a
  tSignal    :: a
  tString    :: a
  tFun1      :: arg -> arg -> a
  tMacro     :: arg -> a
  tType      :: a
  tDatatype  :: Datatype -> [arg] -> a
  tSchemaVar :: Natural -> [arg] -> a
  tMetaVar   :: MetaPtr -> a

instance TyLike (TyF a) a where
  tSyntax         = TyF TSyntax []
  tSignal         = TyF TSignal []
  tString         = TyF TString []
  tFun1 t1 t2     = TyF TFun [t1, t2]
  tMacro t        = TyF TMacro [t]
  tType           = TyF TType []
  tDatatype x ts  = TyF (TDatatype x) ts
  tSchemaVar x ts = TyF (TSchemaVar x) ts
  tMetaVar x      = TyF (TMetaVar x) []

instance TyLike Ty Ty where
  tSyntax         = Ty $ tSyntax
  tSignal         = Ty $ tSignal
  tString         = Ty $ tString
  tFun1 t1 t2     = Ty $ tFun1 t1 t2
  tMacro t        = Ty $ tMacro t
  tType           = Ty $ tType
  tDatatype x ts  = Ty $ tDatatype x ts
  tSchemaVar x ts = Ty $ tSchemaVar x ts
  tMetaVar x      = Ty $ tMetaVar x

tFun :: [Ty] -> Ty -> Ty
tFun args result = foldr tFun1 result args
