{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
module Type.Context where

import Control.Lens

import Env
import Phase

import Util.Store (Store)
import qualified Util.Store as St

newtype TypeContext v t = TypeContext (Store Phase (Env v t))
  deriving Show

instance Ord v => Semigroup (TypeContext v t) where
  TypeContext γ1 <> TypeContext γ2 = TypeContext (St.unionWith (<>) γ1 γ2)

instance Ord v => Monoid (TypeContext v t) where
  mempty = TypeContext mempty

type instance Index (TypeContext v a) = Phase
type instance IxValue (TypeContext v a) = Env v a

instance Ord v => Ixed (TypeContext v a) where
  ix var f (TypeContext env) = TypeContext <$> ix var f env

instance Ord v => At (TypeContext v a) where
  at x f (TypeContext env) = TypeContext <$> at x f env

instance Phased (TypeContext v t) where
  shift i (TypeContext γ) = TypeContext (St.mapKeys (shift i) γ)
