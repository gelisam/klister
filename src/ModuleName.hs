module ModuleName (
  -- * Module names
    ModuleName
  , moduleNameFromLocatedPath
  , moduleNameFromPath
  , moduleNameToPath
  , moduleNameText
  ) where

import Alpha
import Control.Lens
import Control.Monad
import Data.Text (Text)
import qualified Data.Text as T
import System.Directory
import System.FilePath

import Syntax.SrcLoc

newtype ModuleName = ModuleName FilePath
  deriving (Eq, Ord, Show)

moduleNameFromPath :: FilePath -> IO ModuleName
moduleNameFromPath file = ModuleName <$> canonicalizePath file

moduleNameFromLocatedPath :: SrcLoc -> FilePath -> IO ModuleName
moduleNameFromLocatedPath loc file = do
  origDir <- takeDirectory <$> canonicalizePath (view srcLocFilePath loc)
  withCurrentDirectory origDir $ moduleNameFromPath file

moduleNameToPath :: ModuleName -> FilePath
moduleNameToPath (ModuleName file) = file


moduleNameText :: ModuleName -> Text
moduleNameText (ModuleName f) = T.pack f

