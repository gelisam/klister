{-# LANGUAGE TemplateHaskell #-}
module PartialType where

import Control.Lens

import Type

newtype PartialType = PartialType
  { unPartialType :: Maybe (TyF PartialType) }
  deriving (Eq, Show)
makePrisms ''PartialType

nonPartialType :: Ty -> PartialType
nonPartialType = PartialType . Just . fmap nonPartialType . unTy

runPartialType :: PartialType -> Maybe Ty
runPartialType (PartialType Nothing) = Nothing
runPartialType (PartialType (Just t)) =
  traverse runPartialType t >>= pure . Ty
