{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Module (
    Module(..)
  , moduleName
  , moduleImports
  , moduleExports
  , moduleBody
  , CompleteModule(..)
  , _Expanded
  , _KernelModule
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
import Control.Monad.IO.Class
import Data.Data (Data)
import Data.Functor
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Sequence (Seq)
import Data.Text (Text)
import Numeric.Natural

import Binding
import Core
import Datatype
import Kind
import ModuleName
import Phase
import Syntax
import Syntax.SrcLoc
import Type
import Unique

import Util.Key
import Util.Store (Store)
import qualified Util.Store as S

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
  deriving (Data, Show, Eq)

newtype Imports = Imports (HashMap ModuleName (Store Phase (Set Text)))
  deriving (Data, Show)

instance Phased Imports where
  shift i (Imports imports) = Imports (HM.map (S.mapKeys (+ Phase i)) imports)

noImports :: Imports
noImports = Imports mempty

instance Semigroup Imports where
  Imports i1 <> Imports i2 = Imports (HM.unionWith (S.unionWith Set.union) i1 i2)

instance Monoid Imports where
  mempty = noImports
  mappend = (<>)

newtype Exports = Exports (Store Phase (HashMap Text Binding))
  deriving (Data, Show)

instance Phased Exports where
  shift i (Exports exports) = Exports $ S.mapKeys (+ Phase i) exports

instance Semigroup Exports where
  Exports m1 <> Exports m2 = Exports $ S.unionWith (flip (<>)) m1 m2

instance Monoid Exports where
  mempty = noExports
  mappend = (<>)

forExports :: Applicative f => (Phase -> Text -> Binding -> f a) -> Exports -> f [a]
forExports act (Exports todo) =
  traverse (\(x,y,z) -> act x y z)
    [ (p, n, b)
    | (p, m) <- S.toList todo
    , (n, b) <- HM.toList m
    ]

forExports_ :: Applicative f => (Phase -> Text -> Binding -> f a) -> Exports -> f ()
forExports_ act es = forExports act es $> ()

getExport :: Phase -> Text -> Exports -> Maybe Binding
getExport p x (Exports es) = view (at p) es >>= view (at x)

addExport :: Phase -> Text -> Binding -> Exports -> Exports
addExport p x b (Exports es) = Exports $ over (at p) (Just . ins) es
  where
    ins Nothing = HM.singleton x b
    ins (Just m) = HM.insert x b m

noExports :: Exports
noExports = Exports mempty

mapExportNames :: (Text -> Text) -> Exports -> Exports
mapExportNames f (Exports es) = Exports $ fmap (HM.mapKeys f) es

filterExports :: (Phase -> Text -> Bool) -> Exports -> Exports
filterExports ok (Exports es) =
  Exports $ S.mapMaybeWithKey helper es
  where
    helper p bs =
      let out = HM.filterWithKey (\t _ -> ok p t) bs
      in if HM.null out then Nothing else Just out

data ExportSpec
  = ExportIdents [Ident]
  | ExportRenamed ExportSpec [(Text, Text)]
  | ExportPrefixed ExportSpec Text
  | ExportShifted ExportSpec Natural
  deriving (Data, Show, Eq)

data Module f a = Module
  { _moduleName :: ModuleName
  , _moduleImports :: !Imports
  , _moduleBody :: f a
  , _moduleExports :: !Exports
  }
  deriving (Data, Functor, Show)
makeLenses ''Module


newtype CompleteDecl = CompleteDecl { _completeDecl :: Decl Ty (Scheme Ty) (Seq CompleteDecl) Core }
  deriving (Data, Show, Eq)

instance Phased CompleteDecl where
  {-# INLINE shift #-}
  shift i (CompleteDecl d) = CompleteDecl (shift i d)

data CompleteModule
  = Expanded !(Module Seq CompleteDecl) !BindingTable
  | KernelModule !Phase
  deriving (Data, Show)

instance Phased CompleteModule where
  {-# INLINE shift #-}
  shift i (Expanded m bs) = Expanded (shift i m) (shift i bs)
  shift i (KernelModule p) = KernelModule (shift i p)

instance (Functor f, Phased a) => Phased (Module f a) where
  shift i =
    over moduleImports (shift i) .
    over moduleExports (shift i) .
    over moduleBody (fmap (shift i))


newtype DeclPtr = DeclPtr Unique
  deriving newtype (Eq, Ord, HasKey)

instance Show DeclPtr where
  show (DeclPtr u) = "(DeclPtr " ++ show (hashUnique u) ++ ")"

newDeclPtr :: IO DeclPtr
newDeclPtr = DeclPtr <$> newUnique

data Decl ty scheme decl expr
  = Define Ident Var scheme expr
  | DefineMacros [(Ident, MacroVar, expr)]
  | Meta decl
  | Example SrcLoc scheme expr
  | Run SrcLoc expr
  | Import ImportSpec
  | Export ExportSpec
  | Data Ident DatatypeName [Kind] [(Ident, Constructor, [ty])]
    -- ^ User-written name, internal name, type-argument kinds, constructors
  deriving (Data, Functor, Show, Eq)


instance Bifunctor (Decl ty scheme) where
  bimap _f g (Define x v t e) = Define x v t (g e)
  bimap _f g (DefineMacros ms) = DefineMacros [(x, v, g e) | (x, v, e) <- ms]
  bimap f _g (Meta d) = Meta (f d)
  bimap _f g (Example loc t e) = Example loc t (g e)
  bimap _f g (Run loc e) = Run loc (g e)
  bimap _f _g (Import spec) = Import spec
  bimap _f _g (Export spec) = Export spec
  bimap _f _g (Data x dn argKinds ctors) = Data x dn argKinds ctors

instance (Phased decl, Phased expr) => Phased (Decl ty scheme decl expr) where
  shift i = bimap (shift i) (shift i)

newtype DeclTreePtr = DeclTreePtr Unique
  deriving newtype (Eq, Ord, HasKey)

instance Show DeclTreePtr where
  show (DeclTreePtr u) = "(DeclTreePtr " ++ show (hashUnique u) ++ ")"

newDeclTreePtr :: MonadIO m => m DeclTreePtr
newDeclTreePtr = DeclTreePtr <$> liftIO newUnique


data DeclTreeF decl next
  = DeclTreeLeaf
  | DeclTreeAtom decl
  | DeclTreeBranch next next

data SplitDeclTree a = SplitDeclTree
  { _splitDeclTreeRoot :: DeclTreePtr
  , _splitDeclTreeDescendents :: Store DeclTreePtr (DeclTreeF a DeclTreePtr)
  }

makeLenses ''CompleteDecl
makePrisms ''CompleteModule
