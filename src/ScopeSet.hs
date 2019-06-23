{-# LANGUAGE DeriveFunctor, OverloadedStrings, TemplateHaskell #-}
module ScopeSet where

import Control.Lens
import Control.Monad
import qualified Data.Set as Set

import Alpha
import Scope


newtype ScopeSet = ScopeSet
  { unScopeSet :: Set.Set Scope }
  deriving (Eq, Ord, Show)
makePrisms ''ScopeSet

empty :: ScopeSet
empty = ScopeSet Set.empty

size :: ScopeSet -> Int
size = Set.size . unScopeSet

insert :: Scope -> ScopeSet -> ScopeSet
insert x (ScopeSet xs) = ScopeSet (Set.insert x xs)

delete :: Scope -> ScopeSet -> ScopeSet
delete x (ScopeSet xs) = ScopeSet (Set.delete x xs)

member :: Scope -> ScopeSet -> Bool
member x (ScopeSet xs) = x `Set.member` xs

isSubsetOf :: ScopeSet -> ScopeSet -> Bool
isSubsetOf (ScopeSet xs) (ScopeSet ys) = Set.isSubsetOf xs ys


instance AlphaEq ScopeSet where
  alphaCheck x y = guard (x == y)
