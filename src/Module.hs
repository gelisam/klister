{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
module Module (
    Module(..)
  , moduleName
  , moduleImports
  , moduleExports
  , moduleBody
  , CompleteModule(..)
  , CompleteDecl(..)
  , completeDecl
  , Decl(..)
  , Imports
  , noImports
  , ImportSpec(..)
  , ExportSpec(..)
  , Exports
  , getExport
  , addExport
  , mapExportNames
  , filterExports
  , noExports
  , forExports
  , forExports_
  , ModulePtr
  , newModulePtr
  , DeclTreePtr
  , newDeclTreePtr
  , DeclTreeF(..)
  , SplitDeclTree(..)
  , DeclPtr
  , newDeclPtr
  , BindingTable
  ) where

import Control.Lens
import Data.Functor
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Unique
import Numeric.Natural

import Binding
import Core
import Datatype
import ModuleName
import Phase
import Syntax
import Syntax.SrcLoc
import Type


newtype ModulePtr = ModulePtr Unique
  deriving (Eq, Ord)

instance Show ModulePtr where
  show (ModulePtr u) = "(ModulePtr " ++ show (hashUnique u) ++ ")"

newModulePtr :: IO ModulePtr
newModulePtr = ModulePtr <$> newUnique

data ImportSpec
  = ImportModule (Stx ModuleName)
  | ImportOnly ImportSpec [Ident]
  | ShiftImports ImportSpec Natural
  | RenameImports ImportSpec [(Ident, Ident)]
  | PrefixImports ImportSpec Text
  deriving Show

newtype Imports = Imports (Map ModuleName (Map Phase (Set Text)))
  deriving Show

instance Phased Imports where
  shift i (Imports imports) = Imports (Map.map (Map.mapKeys (shift i)) imports)

noImports :: Imports
noImports = Imports Map.empty

instance Semigroup Imports where
  Imports i1 <> Imports i2 = Imports (Map.unionWith (Map.unionWith Set.union) i1 i2)

instance Monoid Imports where
  mempty = noImports
  mappend = (<>)

newtype Exports = Exports (Map Phase (Map Text Binding))
  deriving Show

instance Phased Exports where
  shift i (Exports exports) = Exports $ Map.mapKeys (shift i) exports

instance Semigroup Exports where
  Exports m1 <> Exports m2 = Exports $ Map.unionWith (flip (<>)) m1 m2

instance Monoid Exports where
  mempty = noExports
  mappend = (<>)

forExports :: Applicative f => (Phase -> Text -> Binding -> f a) -> Exports -> f [a]
forExports act (Exports todo) =
  traverse (\(x,y,z) -> act x y z)
    [ (p, n, b)
    | (p, m) <- Map.toList todo
    , (n, b) <- Map.toList m
    ]

forExports_ :: Applicative f => (Phase -> Text -> Binding -> f a) -> Exports -> f ()
forExports_ act es = forExports act es $> ()

getExport :: Phase -> Text -> Exports -> Maybe Binding
getExport p x (Exports es) = view (at p) es >>= view (at x)

addExport :: Phase -> Text -> Binding -> Exports -> Exports
addExport p x b (Exports es) = Exports $ over (at p) (Just . ins) es
  where
    ins Nothing = Map.singleton x b
    ins (Just m) = Map.insert x b m

noExports :: Exports
noExports = Exports Map.empty

mapExportNames :: (Text -> Text) -> Exports -> Exports
mapExportNames f (Exports es) = Exports $ Map.map (Map.mapKeys f) es

filterExports :: (Phase -> Text -> Bool) -> Exports -> Exports
filterExports ok (Exports es) =
  Exports $ Map.mapMaybeWithKey helper es
  where
    helper p bs =
      let out = Map.filterWithKey (\t _ -> ok p t) bs
      in if Map.null out then Nothing else Just out

data ExportSpec
  = ExportIdents [Ident]
  | ExportRenamed ExportSpec [(Text, Text)]
  | ExportPrefixed ExportSpec Text
  | ExportShifted ExportSpec Natural
  deriving Show

data Module f a = Module
  { _moduleName :: ModuleName
  , _moduleImports :: !Imports
  , _moduleBody :: f a
  , _moduleExports :: !Exports
  }
  deriving (Functor, Show)
makeLenses ''Module


newtype CompleteDecl = CompleteDecl { _completeDecl :: Decl Ty (Scheme Ty) [CompleteDecl] Core }
  deriving Show

instance Phased CompleteDecl where
  shift i (CompleteDecl d) = CompleteDecl (shift i d)

data CompleteModule
  = Expanded !(Module [] CompleteDecl) !BindingTable
  | KernelModule !Phase
  deriving Show

instance Phased CompleteModule where
  shift i (Expanded m bs) = Expanded (shift i m) (shift i bs)
  shift i (KernelModule p) = KernelModule (shift i p)

instance (Functor f, Phased a) => Phased (Module f a) where
  shift i =
    over moduleImports (shift i) .
    over moduleExports (shift i) .
    over moduleBody (fmap (shift i))


newtype DeclPtr = DeclPtr Unique
  deriving (Eq, Ord)

instance Show DeclPtr where
  show (DeclPtr u) = "(DeclPtr " ++ show (hashUnique u) ++ ")"

newDeclPtr :: IO DeclPtr
newDeclPtr = DeclPtr <$> newUnique

data Decl ty scheme decl expr
  = Define Ident Var scheme expr
  | DefineMacros [(Ident, MacroVar, expr)]
  | Meta decl
  | Example SrcLoc scheme expr
  | Import ImportSpec
  | Export ExportSpec
  | Data Ident DatatypeName Natural [(Ident, Constructor, [ty])]
    -- ^ User-written name, internal name, arity, constructors
  deriving (Functor, Show)

instance Bifunctor (Decl ty scheme) where
  bimap _f g (Define x v t e) = Define x v t (g e)
  bimap _f g (DefineMacros ms) = DefineMacros [(x, v, g e) | (x, v, e) <- ms]
  bimap f _g (Meta d) = Meta (f d)
  bimap _f g (Example loc t e) = Example loc t (g e)
  bimap _f _g (Import spec) = Import spec
  bimap _f _g (Export spec) = Export spec
  bimap _f _g (Data x dn arity ctors) = Data x dn arity ctors

instance (Phased decl, Phased expr) => Phased (Decl ty scheme decl expr) where
  shift i = bimap (shift i) (shift i)

newtype DeclTreePtr = DeclTreePtr Unique
  deriving (Eq, Ord)

instance Show DeclTreePtr where
  show (DeclTreePtr u) = "(DeclTreePtr " ++ show (hashUnique u) ++ ")"

newDeclTreePtr :: IO DeclTreePtr
newDeclTreePtr = DeclTreePtr <$> newUnique


data DeclTreeF decl next
  = DeclTreeLeaf
  | DeclTreeAtom decl
  | DeclTreeBranch next next

data SplitDeclTree a = SplitDeclTree
  { _splitDeclTreeRoot :: DeclTreePtr
  , _splitDeclTreeDescendents :: Map DeclTreePtr (DeclTreeF a DeclTreePtr)
  }

makeLenses ''CompleteDecl
