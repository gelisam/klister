-- | Internal module for Syntax component. Holds core data types, classes and
-- smart constructors.

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE CPP                #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Syntax.Syntax where

import Control.Lens hiding (List)
import Data.Data (Data)
import Data.Text (Text)

import Alpha
import ModuleName
import Phase
import Scope
import ScopeSet
import Syntax.SrcLoc

import qualified Util.Set   as Set
import qualified Util.Store as St


data Stx a = Stx
  { _stxScopeSet :: ScopeSet
  , _stxSrcLoc   :: !SrcLoc
  , _stxValue    :: a
  }
  deriving (Data, Eq, Functor, Show)
makeLenses ''Stx

data ExprF a
  = Id Text
  | String Text
  | Integer Integer
  | List [a]
  deriving (Data, Eq, Functor, Show)
makePrisms ''ExprF


newtype Syntax = Syntax { _unSyntax :: (Stx (ExprF Syntax)) }
  deriving (Data, Eq, Show)
makeLenses ''Syntax

type Ident = Stx Text

data ParsedModule a = ParsedModule
  { _moduleSource :: ModuleName
  , _moduleLanguage :: a
  , _moduleContents :: a
  }
  deriving (Eq, Show)
makeLenses ''ParsedModule

class HasScopes a where
  getScopes :: a -> ScopeSet
  adjustScope :: (Scope -> ScopeSet -> ScopeSet) -> Scope -> a -> a
  mapScopes :: (ScopeSet -> ScopeSet) -> a -> a

instance HasScopes (Stx Text) where
  getScopes (Stx scs _ _) = scs
  adjustScope f sc (Stx scs srcloc x) = Stx (f sc scs) srcloc x
  mapScopes f (Stx scs srcloc x) = Stx (f scs) srcloc x

instance HasScopes Syntax where
  getScopes (Syntax (Stx scs _ _)) = scs
  adjustScope f sc = mapScopes (f sc)
  mapScopes f (Syntax (Stx scs srcloc e)) =
    Syntax $
    Stx (f scs) srcloc $
    mapRec e
    where
      mapRec (Id x) = Id x
      mapRec (String str) = String str
      mapRec (Integer i) = Integer i
      mapRec (List xs) = List $ map (\stx -> mapScopes f stx) xs

instance Phased (Stx Text) where
  shift i = mapScopes (shift i)

instance Phased Syntax where
  shift i = mapScopes (shift i)

instance AlphaEq a => AlphaEq (Stx a) where
  alphaCheck (Stx scopeSet1 srcLoc1 x1)
             (Stx scopeSet2 srcLoc2 x2) = do
    alphaCheck scopeSet1 scopeSet2
    alphaCheck srcLoc1   srcLoc2
    alphaCheck x1        x2

instance AlphaEq a => AlphaEq (ExprF a) where
  alphaCheck (Id x1)
             (Id x2) = do
    alphaCheck x1 x2
  alphaCheck (List xs1)
             (List xs2) = do
    alphaCheck xs1 xs2
  alphaCheck _ _ = notAlphaEquivalent

instance AlphaEq Syntax where
  alphaCheck (Syntax x1)
             (Syntax x2) = do
    alphaCheck x1 x2


addScopes' :: HasScopes p => ScopeSet -> p -> p
#ifndef KDEBUG
addScopes' scopeSet =  mapScopes (over phaseScopes newSpecificScopes
                                 . over universalScopes newUniversalScopes)
  where
    newUniversalScopes = Set.union (view _1 (contents scopeSet))
    newSpecificScopes  = St.unionWith (<>) (view _2 (contents scopeSet))
#else
addScopes' scopeSet
  = addSpecificScopes
  . addUniversalScopes
  where
    addUniversalScopes :: HasScopes a => a -> a
    addUniversalScopes a0 =
      foldlOf (to ScopeSet.contents . _1 . folded)
              (flip addScope')
              a0
              scopeSet

    addSpecificScopes :: HasScopes a => a -> a
    addSpecificScopes a0 =
      ifoldlOf (to ScopeSet.contents .> _2 .> ifolded <. folded)
               (\p a sc -> addScope p sc a)
               a0
               scopeSet
#endif
