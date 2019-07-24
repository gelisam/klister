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
import Data.Text (Text)
import qualified Data.Text as T
import System.Directory
import System.FilePath

import Syntax.SrcLoc

newtype KernelName = Kernel ()
  deriving (Eq, Ord, Show)

kernelName :: KernelName
kernelName = Kernel ()

data ModuleName = ModuleName FilePath | KernelName KernelName
  deriving (Eq, Ord, Show)

moduleNameFromPath :: FilePath -> IO ModuleName
moduleNameFromPath file = ModuleName <$> canonicalizePath file

moduleNameFromLocatedPath :: SrcLoc -> FilePath -> IO ModuleName
moduleNameFromLocatedPath loc file = do
  origDir <- takeDirectory <$> canonicalizePath (view srcLocFilePath loc)
  withCurrentDirectory origDir $ moduleNameFromPath file

moduleNameToPath :: ModuleName -> Either FilePath KernelName
moduleNameToPath (ModuleName file) = Left file
moduleNameToPath (KernelName _) = Right (Kernel ())


moduleNameText :: ModuleName -> Text
moduleNameText (ModuleName f) = T.pack (show f)
moduleNameText (KernelName _) = T.pack "kernel"

