{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
module Env (Env, empty, insert, lookup, lookupVal) where

import Prelude hiding (lookup)

import Control.Lens
import Data.Map (Map)
import qualified Data.Map as Map

import Core (Var(..))
import Syntax (Ident)

newtype Env a = Env (Map Var (Ident, a))
  deriving (Eq, Show)

empty :: Env a
empty = Env (Map.empty)

insert :: Var -> Ident -> a -> Env a -> Env a
insert x n v (Env env) = Env (Map.insert x (n, v) env)

lookup :: Var -> Env a -> Maybe (Ident, a)
lookup x (Env env) = Map.lookup x env

lookupVal :: Var -> Env a -> Maybe a
lookupVal x env = snd <$> lookup x env

type instance Index (Env a) = Var
type instance IxValue (Env a) = (Ident, a)

instance Ixed (Env a) where
  ix var f (Env env) = Env <$> ix var f env

instance At (Env a) where
  at x f (Env env) = Env <$> at x f env
