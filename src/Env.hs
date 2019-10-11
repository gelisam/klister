{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
module Env (Env, empty, insert, singleton, lookup, lookupIdent, lookupVal, toList, named) where

import Prelude hiding (lookup)

import Control.Lens
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)

import Syntax (Ident, Stx(..))

newtype Env v a = Env (Map v (Ident, a))
  deriving (Eq, Functor, Monoid, Semigroup, Show)

empty :: Env v a
empty = Env (Map.empty)

toList :: Env v a -> [(v, Ident, a)]
toList (Env env) = [(x, n, v) | (x, (n, v)) <- Map.toList env]

singleton :: v -> Ident -> a -> Env v a
singleton x n v = Env (Map.singleton x (n, v))

insert :: Ord v => v -> Ident -> a -> Env v a -> Env v a
insert x n v (Env env) = Env (Map.insert x (n, v) env)

lookup :: Ord v => v -> Env v a -> Maybe (Ident, a)
lookup x (Env env) = Map.lookup x env

lookupVal :: Ord v => v -> Env v a -> Maybe a
lookupVal x env = snd <$> lookup x env

lookupIdent :: Ord v => v -> Env v a -> Maybe Ident
lookupIdent x env = fst <$> lookup x env

named :: Text -> Env v a -> [(v, a)]
named n (Env xs) = [(x, a) | (x, (Stx _ _ n', a)) <- Map.toList xs, n == n']

type instance Index (Env v a) = v
type instance IxValue (Env v a) = (Ident, a)

instance Ord v => Ixed (Env v a) where
  ix var f (Env env) = Env <$> ix var f env

instance Ord v => At (Env v a) where
  at x f (Env env) = Env <$> at x f env
