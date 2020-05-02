module ModuleName (
  -- * Module names
    ModuleName(..)
  , KernelName
  , kernelName
  , moduleNameFromLocatedPath
  , moduleNameFromPath
  , moduleNameToPath
  , moduleNameText
  ) where

import Control.Lens
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import System.Directory
import System.FilePath

import KlisterPath
import ShortShow
import Syntax.SrcLoc

newtype KernelName = Kernel ()
  deriving (Eq, Ord, Show)

kernelName :: KernelName
kernelName = Kernel ()

data ModuleName = ModuleName FilePath | KernelName KernelName
  deriving (Eq, Ord, Show)

instance ShortShow ModuleName where
  shortShow (ModuleName x) = x
  shortShow (KernelName _k) = "kernel"

moduleNameFromPath :: FilePath -> IO ModuleName
moduleNameFromPath file = ModuleName <$> canonicalizePath file

moduleNameFromLocatedPath ::
  KlisterPath {- ^ Path to search -} ->
  SrcLoc ->
  String {- ^ Module name -} ->
  IO (Either KlisterPathError ModuleName)
moduleNameFromLocatedPath klisterPath loc name = do
  sameDir <- makeKlisterPath (Set.singleton (takeDirectory (view srcLocFilePath loc)))
  maybePath <- importFromKlisterPath (sameDir <> klisterPath) name
  case maybePath of
    Left err -> pure (Left err)
    Right path -> Right <$> moduleNameFromPath path

moduleNameToPath :: ModuleName -> Either FilePath KernelName
moduleNameToPath (ModuleName file) = Left file
moduleNameToPath (KernelName _) = Right (Kernel ())


moduleNameText :: ModuleName -> Text
moduleNameText (ModuleName f) = T.pack (show f)
moduleNameText (KernelName _) = T.pack "kernel"

