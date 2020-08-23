{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module Kind (Kind(..), KindVar, newKindVar, kFun, KindStore) where

import Control.Lens
import Data.Map.Strict (Map)
import Data.Unique

newtype KindVar = KindVar Unique deriving (Eq, Ord)

instance Show KindVar where
  show (KindVar i) = "(KindVar " ++ show (hashUnique i) ++ ")"

data Kind
  = KStar
  | KFun Kind Kind
  | KMetaVar KindVar
  deriving (Show, Eq)
makePrisms ''Kind


newKindVar :: IO KindVar
newKindVar = KindVar <$> newUnique


kFun :: [Kind] -> Kind -> Kind
kFun args result = foldr KFun result args

newtype KindStore = KindStore (Map KindVar Kind)
  deriving (Monoid, Semigroup, Show)

type instance Index KindStore = KindVar
type instance IxValue KindStore = Kind

instance Ixed KindStore where
  ix var f (KindStore env) = KindStore <$> ix var f env

instance At KindStore where
  at x f (KindStore env) = KindStore <$> at x f env

