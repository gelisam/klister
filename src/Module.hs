{-# LANGUAGE DeriveFunctor #-}
module Module where

import Data.Unique

import Core
import Syntax

newtype ModuleName = ModuleName FilePath
  deriving (Eq, Ord, Show)

newtype ModulePtr = ModulePtr Unique
  deriving (Eq, Ord)

newModulePtr :: IO ModulePtr
newModulePtr = ModulePtr <$> newUnique

type Imports = () -- TODO
type Exports = () -- TODO

data Module a = Module ModuleName Imports [a] Exports
  deriving (Functor, Show)


newtype DeclPtr = DeclPtr Unique

newDeclPtr :: IO DeclPtr
newDeclPtr = DeclPtr <$> newUnique

data Decl a
  = Define Ident Var a
  | DefineMacro Ident Var a
  | Meta [Decl a]
  | Example a
  deriving (Functor, Show)
