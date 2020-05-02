module ModuleName (
  -- * Module names
    ModuleName(..)
  , KernelName
  , kernelName
  , moduleNameFromPath
  , moduleNameToPath
  , moduleNameText
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import System.Directory

import ShortShow

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

moduleNameToPath :: ModuleName -> Either FilePath KernelName
moduleNameToPath (ModuleName file) = Left file
moduleNameToPath (KernelName _) = Right (Kernel ())

moduleNameText :: ModuleName -> Text
moduleNameText (ModuleName f) = T.pack (show f)
moduleNameText (KernelName _) = T.pack "kernel"

