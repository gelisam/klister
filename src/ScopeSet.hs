{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module ScopeSet (
  -- * Scope Sets and their construction
    ScopeSet
  , empty
  -- * Queries
  , size
  , member
  , isSubsetOf
  -- * Updates
  , insertAtPhase
  , insertUniversally
  , deleteAtPhase
  , deleteUniversally
  ) where

import Control.Lens
import Control.Monad
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Alpha
import Phase
import Scope

data ScopeSet = ScopeSet
  { _universalScopes :: Set Scope
  , _phaseScopes :: Map Phase (Set Scope)
  }
  deriving (Eq, Ord, Show)
makeLenses ''ScopeSet

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
               maybe (Set.empty) id (view (phaseScopes . at p) scs)

size :: Phase -> ScopeSet -> Int
size p = Set.size . scopes p

insertAtPhase :: Phase -> Scope -> ScopeSet -> ScopeSet
insertAtPhase p sc scs = over (phaseScopes . at p) ins scs
  where
    ins :: Maybe (Set Scope) -> Maybe (Set Scope)
    ins = maybe (Just (Set.singleton sc)) (Just . Set.insert sc)

insertUniversally :: Scope -> ScopeSet -> ScopeSet
insertUniversally sc scs = over universalScopes (Set.insert sc) scs

member :: Phase -> Scope -> ScopeSet -> Bool
member p sc scs = sc `Set.member` (scopes p scs)

instance Phased ScopeSet where
  shift j = over phaseScopes $ Map.mapKeys (shift j)

isSubsetOf :: Phase -> ScopeSet -> ScopeSet -> Bool
isSubsetOf p scs1 scs2 =
  Set.isSubsetOf (scopes p scs1) (scopes p scs2)

deleteAtPhase :: Phase -> Scope -> ScopeSet -> ScopeSet
deleteAtPhase p sc scs = over (phaseScopes . at p) del scs
  where
    del = fmap (Set.delete sc)

deleteUniversally :: Scope -> ScopeSet -> ScopeSet
deleteUniversally sc scs =
  over phaseScopes (Map.map (Set.delete sc)) $
  over universalScopes (Set.delete sc) scs

instance AlphaEq ScopeSet where
  alphaCheck x y = guard (x == y)
