{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
module Type.Context where

import Control.Lens
import Data.Map (Map)
import qualified Data.Map as Map

import Env
import Phase

newtype TypeContext v t = TypeContext (Map Phase (Env v t))

instance Ord v => Semigroup (TypeContext v t) where
  TypeContext γ1 <> TypeContext γ2 = TypeContext (Map.unionWith (<>) γ1 γ2)

instance Ord v => Monoid (TypeContext v t) where
  mempty = TypeContext Map.empty

type instance Index (TypeContext v a) = Phase
type instance IxValue (TypeContext v a) = Env v a

instance Ord v => Ixed (TypeContext v a) where
  ix var f (TypeContext env) = TypeContext <$> ix var f env

instance Ord v => At (TypeContext v a) where
  at x f (TypeContext env) = TypeContext <$> at x f env
