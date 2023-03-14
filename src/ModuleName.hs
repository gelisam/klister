{-# LANGUAGE DeriveDataTypeable #-}
module ModuleName (
  -- * Module names
    ModuleName(..)
  , KernelName
  , kernelName
  , moduleNameFromPath
  , moduleNameToPath
  , moduleNameText
  , relativizeModuleName
  ) where

import Data.Data (Data)
import Data.Text (Text)
import qualified Data.Text as T
import System.Directory
import System.FilePath

import ShortShow

newtype KernelName = Kernel ()
  deriving (Data, Eq, Ord, Show)

kernelName :: KernelName
kernelName = Kernel ()

data ModuleName = ModuleName FilePath | KernelName KernelName
  deriving (Data, Eq, Ord, Show)

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

-- | Given a path, relativize the @ModuleName@ with respect to the path.
--
-- > relativizeModuleName "a/b/c/klister" "a/b/c/klister/examples/do.kl" = "examples/do.kl"
--
relativizeModuleName :: FilePath -> ModuleName -> ModuleName
relativizeModuleName l (ModuleName r) = ModuleName (makeRelative l r)
relativizeModuleName _ k@KernelName{} = k
