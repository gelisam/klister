{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RoleAnnotations    #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- | wrapper over IntMap for our purposes

module Util.Store
  ( lookup
  , (!)
  , singleton
  , insert
  , toList
  , toAscList
  , fromList
  , Store
  , unionWith
  , mapKeys
  , mapMaybeWithKey
  )
where

import Prelude hiding (lookup)
import Control.Lens
import Data.Data (Data)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Control.Arrow (first)

import Util.Key
import Phase

newtype Store p v = Store { unStore :: IntMap v}
  deriving newtype (Eq, Ord, Show, Semigroup, Monoid, Functor, Foldable)
  deriving stock   Data
type role Store nominal _

instance Traversable (Store p) where
  traverse f s = Store <$> traverse f (unStore s)

instance  FoldableWithIndex Phase (Store p) where
    ifoldMap f s = IM.foldMapWithKey (f . Phase . fromIntegral  . toInteger) (unStore s)
    {-# INLINE ifoldMap #-}
    ifoldr f acc s = IM.foldrWithKey (f . Phase . fromIntegral  . toInteger) acc (unStore s)
    {-# INLINE ifoldr #-}
    ifoldl' f acc s = IM.foldlWithKey' (\e k ac -> f (fromIntegral k) e ac) acc (unStore s)
    {-# INLINE ifoldl' #-}

type instance IxValue (Store p v) = v
type instance Index   (Store p v) = p

instance HasKey p => Ixed (Store p v) where
  ix k f m = case lookup k m of
    Just v -> f v <&> \new_v -> insert k new_v m
    Nothing -> pure m

instance HasKey p => At (Store p v) where
  at k f s = alterF f k s
  {-# INLINE at #-}

instance (c ~ d) => Each (Store c a) (Store d b) a b where
  each = traversed

lookup :: HasKey p => p -> Store p v -> Maybe v
lookup ptr graph = getKey ptr `IM.lookup` unStore graph

(!) :: HasKey p => Store p v -> p -> v
graph ! ptr = case lookup ptr graph of
  Just v -> v
  Nothing -> error "Store.!!: key not found"

singleton :: HasKey p => p -> v -> Store p v
singleton ptr val = Store $! IM.singleton (getKey ptr) val

insert :: HasKey p => p -> v -> Store p v -> Store p v
insert k v str = Store $! IM.insert (getKey k) v (unStore str)

toList :: HasKey p => Store p v -> [(p,v)]
toList str = map (first fromKey) $ IM.toList (unStore str)

toAscList :: HasKey p => Store p v -> [(p,v)]
toAscList str = map (first fromKey) $ IM.toAscList (unStore str)

fromList :: HasKey p => [(p,v)] -> Store p v
fromList ps = Store $! IM.fromList $ map (first getKey) ps

alterF :: ( Functor f, HasKey p)
       => (Maybe v -> f (Maybe v)) -> p -> Store p v -> f (Store p v)
alterF f k s = Store <$> IM.alterF f (getKey k) (unStore s)

unionWith :: (v -> v -> v) -> Store p v -> Store p v -> Store p v
unionWith f l r = Store $! IM.unionWith f (unStore l) (unStore r)

mapMaybeWithKey :: HasKey p => (p -> a -> Maybe b) -> Store p a -> Store p b
mapMaybeWithKey f s = Store $! IM.mapMaybeWithKey (f . fromKey) (unStore s)

mapKeys :: HasKey p => (p -> p) -> Store p v -> Store p v
mapKeys f s = Store $! IM.mapKeys (getKey . f . fromKey) (unStore s)
