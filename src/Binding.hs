{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Binding where

import Control.Lens
import Data.Data (Data)
import Data.Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import ScopeSet
import Data.Text (Text)
import Data.Sequence (Seq)

import Binding.Info
import Phase
import Syntax.SrcLoc
import Unique

import Util.Key

newtype Binding = Binding Unique
  deriving newtype (Eq, Ord, Hashable)
  deriving stock Data

instance HasKey Binding where
  getKey (Binding u) = getKey u
  fromKey i = Binding $! fromKey i
  {-# INLINE getKey  #-}
  {-# INLINE fromKey #-}

instance Show Binding where
  show (Binding b) = "(Binding " ++ show (hashUnique b) ++ ")"

newtype BindingTable = BindingTable { _bindings :: HashMap Text (Seq (ScopeSet, Binding, BindingInfo SrcLoc)) }
  deriving (Data, Show)
makeLenses ''BindingTable

instance Semigroup BindingTable where
  b1 <> b2 = BindingTable $ HM.unionWith (<>) (view bindings b1) (view bindings b2)

instance Monoid BindingTable where
  mempty = BindingTable HM.empty

instance Phased BindingTable where
  shift i = over bindings (HM.map (fmap (over _1 (shift i))))

type instance Index BindingTable = Text
type instance IxValue BindingTable = Seq (ScopeSet, Binding, BindingInfo SrcLoc)

instance Ixed BindingTable where
  ix x f (BindingTable bs) = BindingTable <$> ix x f bs

instance At BindingTable where
  at x f (BindingTable bs) = BindingTable <$> at x f bs
