{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
module Module where

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
  , _moduleBody :: (f a)
  , _moduleExports :: [Export]
  }
  deriving (Functor, Show)


type CompleteModule = Module [] (Decl [] Core)

newtype DeclPtr = DeclPtr Unique
  deriving (Eq, Ord)

newDeclPtr :: IO DeclPtr
newDeclPtr = DeclPtr <$> newUnique

data Decl f a
  = Define Ident Var a
  | DefineMacro Ident Var a
  | Meta (f (Decl f a))
  | Example a
  deriving (Functor)

instance Show (Decl f a) where
  show _ = "<decl>" -- TODO


newtype ModBodyPtr = ModBodyPtr Unique
  deriving (Eq, Ord)

newModBodyPtr :: IO ModBodyPtr
newModBodyPtr = ModBodyPtr <$> newUnique


data ModuleBodyF decl next = Done | Decl decl next

data SplitModuleBody a = SplitModuleBody
  { _splitModuleRoot :: ModBodyPtr
  , _splitModuleDescendents :: Map ModBodyPtr (ModuleBodyF a ModBodyPtr)
  }
