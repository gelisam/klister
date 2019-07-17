{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
module Module where

import Control.Lens
import Data.Map(Map)
import Data.Unique

import Core
import Syntax


newtype ModuleName = ModuleName FilePath
  deriving (Eq, Ord, Show)

newtype ModulePtr = ModulePtr Unique
  deriving (Eq, Ord)

newModulePtr :: IO ModulePtr
newModulePtr = ModulePtr <$> newUnique

type Import = () -- TODO
type Export = () -- TODO

data Module f a = Module
  { _moduleName :: ModuleName
  , _moduleImports :: [Import]
  , _moduleBody :: f a
  , _moduleExports :: [Export]
  }
  deriving (Functor, Show)
makeLenses ''Module

type CompleteModule = Module [] (Decl Core)


newtype DeclPtr = DeclPtr Unique
  deriving (Eq, Ord)

newDeclPtr :: IO DeclPtr
newDeclPtr = DeclPtr <$> newUnique

data Decl a
  = Define Ident Var a
  | DefineMacros [(Ident, a)]
  | Meta (Decl a)
  | Example a
  deriving (Functor, Show)


newtype ModBodyPtr = ModBodyPtr Unique
  deriving (Eq, Ord)

newModBodyPtr :: IO ModBodyPtr
newModBodyPtr = ModBodyPtr <$> newUnique


data ModuleBodyF decl next = Done | Decl decl next

data SplitModuleBody a = SplitModuleBody
  { _splitModuleRoot :: ModBodyPtr
  , _splitModuleDescendents :: Map ModBodyPtr (ModuleBodyF a ModBodyPtr)
  }
