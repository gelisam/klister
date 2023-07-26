{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE CPP                #-}
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

-- | wrapper over IntSet for our purposes

module Util.Set
  (
#ifndef KDEBUG
    member
  , singleton
  , empty
  , size
  , isSubsetOf
  , insert
  , delete
  , toList
  , fromList
  , Set
  , union
#else
  module Data.Set
#endif
  )
where

import Prelude hiding (lookup)
import Control.Lens
import Data.Data (Data)
import Data.Functor
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Control.Monad (guard)
import Util.Key

#ifdef KDEBUG
import Data.Set
#endif

newtype Set key = Set { unSet :: IntSet}
  deriving newtype (Eq, Ord, Show, Semigroup, Monoid)
  deriving stock   Data
type role Set nominal

type instance IxValue (Set p) = ()
type instance Index   (Set p) = p

instance HasKey p => Ixed (Set p) where
  ix k f m = if member k m
    then f () $> m
    else pure m

instance HasKey p => At (Set p) where
    {-# INLINE at #-}
    at k f s = fmap choose (f (guard member_))
      where
      member_ = member k s

      (inserted, deleted)
        | member_   = (s, delete k s)
        | otherwise = (insert k s, s)

      choose (Just ~()) = inserted
      choose Nothing    = deleted

member :: HasKey e => e -> Set e -> Bool
member e s = IS.member (getKey e) (unSet s)

empty :: Set e
empty = Set IS.empty

size :: Set e -> Int
size = IS.size . unSet

singleton :: HasKey e => e -> Set e
singleton = Set . IS.singleton . getKey

insert :: HasKey e => e -> Set e -> Set e
insert e s = Set $! IS.insert (getKey e) (unSet s)

delete :: HasKey e => e -> Set e -> Set e
delete e s = Set $! IS.delete (getKey e) (unSet s)

isSubsetOf :: Set e -> Set e -> Bool
isSubsetOf l r = IS.isSubsetOf (unSet l) (unSet r)

toList :: HasKey p => Set p -> [p]
toList = map fromKey . IS.toList . unSet

fromList :: HasKey p => [p] -> Set p
fromList = Set . IS.fromList . map getKey

union :: Set p -> Set p -> Set p
union l r = Set $! IS.union (unSet l) (unSet r)
