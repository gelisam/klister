{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
module ScopeSet (
  -- * Scope Sets and their construction
    ScopeSet
  , empty
  , singleScopeAtPhase
  , singleUniversalScope
  -- * Queries
  , size
  , member
  , isSubsetOf
  , contents
  -- * Updates
  , insertAtPhase
  , insertUniversally
  , deleteAtPhase
  , deleteUniversally
  , flipUniversally
  , allScopeSets
  ) where

import Control.Lens
import Control.Monad
import Data.Data (Data, gfoldl)
import Data.Typeable
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Alpha
import Phase
import Scope
import ShortShow

data ScopeSet = ScopeSet
  { _universalScopes :: Set Scope
  , _phaseScopes :: Map Phase (Set Scope)
  }
  deriving (Data, Eq, Ord, Show)
makeLenses ''ScopeSet

instance ShortShow ScopeSet where
  shortShow (ScopeSet always phased) =
    "{" ++ show (Set.toList always) ++ " | " ++ show (Map.toList phased) ++ "}"

instance Semigroup ScopeSet where
  scs1 <> scs2 =
    ScopeSet
      { _universalScopes = view universalScopes scs1 <> view universalScopes scs2
      , _phaseScopes =
        Map.unionWith (<>) (view phaseScopes scs1) (view phaseScopes scs2)
      }

instance Monoid ScopeSet where
  mempty = empty
  mappend = (<>)

empty :: ScopeSet
empty = ScopeSet Set.empty Map.empty

scopes :: Phase -> ScopeSet -> Set Scope
scopes p scs = view universalScopes scs `Set.union`
               view (phaseScopes . at p . non Set.empty) scs

size :: Phase -> ScopeSet -> Int
size p = Set.size . scopes p

singleScopeAtPhase :: Scope -> Phase -> ScopeSet
singleScopeAtPhase sc p = insertAtPhase p sc mempty

singleUniversalScope :: Scope -> ScopeSet
singleUniversalScope sc = insertUniversally sc mempty

insertAtPhase :: Phase -> Scope -> ScopeSet -> ScopeSet
insertAtPhase p sc = set (phaseScopes . at p . non Set.empty . at sc)
                         (Just ())

insertUniversally :: Scope -> ScopeSet -> ScopeSet
insertUniversally sc = set (universalScopes . at sc)
                           (Just ())

member :: Phase -> Scope -> ScopeSet -> Bool
member p sc scs = sc `Set.member` (scopes p scs)

instance Phased ScopeSet where
  shift j = over phaseScopes $ Map.mapKeys (shift j)

isSubsetOf :: Phase -> ScopeSet -> ScopeSet -> Bool
isSubsetOf p scs1 scs2 =
  Set.isSubsetOf (scopes p scs1) (scopes p scs2)

deleteAtPhase :: Phase -> Scope -> ScopeSet -> ScopeSet
deleteAtPhase p sc = set (phaseScopes . at p . non Set.empty . at sc)
                         Nothing

deleteUniversally :: Scope -> ScopeSet -> ScopeSet
deleteUniversally sc = set (phaseScopes . each . at sc)
                           Nothing
                     . set (universalScopes . at sc)
                           Nothing

flipUniversally :: Scope -> ScopeSet -> ScopeSet
flipUniversally sc = over (phaseScopes . each . at sc) flipper .
                     over (universalScopes . at sc) flipper
  where
    flipper (Just ()) = Nothing
    flipper Nothing = Just ()

contents :: ScopeSet -> (Set Scope, Map Phase (Set Scope))
contents scs = (view universalScopes scs, view phaseScopes scs)

instance AlphaEq ScopeSet where
  alphaCheck x y = guard (x == y)

allScopeSets :: Data d => Traversal' d ScopeSet
allScopeSets = allScopeSets'
  where
    allScopeSets' :: forall f d. (Applicative f, Data d)
                  => (ScopeSet -> f ScopeSet)
                  -> d -> f d
    allScopeSets' f = gmapA go
      where
        go :: forall a. Data a => a -> f a
        go a = case eqT @a @ScopeSet of
          Just Refl -> f a
          Nothing -> allScopeSets' f a

    -- A variant of Data.Data.gmapM which uses Applicative instead of Monad
    gmapA :: forall f d. (Applicative f, Data d)
          => (forall x. Data x => x -> f x)
          -> d -> f d
    gmapA g = gfoldl combine pure
      where
        combine :: Data a => f (a -> b) -> a -> f b
        combine ff a = (<*>) ff (g a)
