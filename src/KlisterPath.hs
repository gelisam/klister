{-
Module           : KlisterPath
Description      : Searching for imports
Copyright        : (c) Klister Collaborators 2020
License          : See GH#55
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

Klister executes the following procedure when searching for imports:

1. Check for files with the given name in the same directory as the importing
   file
2. Check for modules in the stdlib
3. Check for modules in directories listed in the @KLISTERPATH@ environment
   variable

The stdlib modules are installed by Cabal, and accessed via the generated module
"Paths_klister".
-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module KlisterPath
  ( KlisterPath
  , KlisterPathError(..)
  , ppKlisterPathError
  , getKlisterPath
  , findModule
  ) where

import Control.Lens (view)
import Data.Functor ((<&>))
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text.Prettyprint.Doc as PP
import System.Directory (canonicalizePath, listDirectory)
import System.FilePath (takeDirectory)
import System.FilePath.Posix ((</>))
import System.Environment (lookupEnv)

import ModuleName
import Syntax.SrcLoc
import Paths_klister (getDataDir)

-- | A list of directories to search for modules
--
-- Invariant: All paths are canonical.
newtype KlisterPath = KlisterPath { unKlisterPath :: Set FilePath }
  deriving (Monoid, Semigroup, Show)

makeKlisterPath :: Set FilePath -> IO KlisterPath
makeKlisterPath paths =
  KlisterPath . Set.fromList <$>
    mapM canonicalizePath (Set.toList paths)

-- | Fetch the Klister path from the environment variable @KLISTERPATH@.
getKlisterPath :: IO KlisterPath
getKlisterPath =
  makeKlisterPath =<<
    maybe Set.empty (Set.fromList . (split ':')) <$>
      lookupEnv "KLISTERPATH"
  where
    -- How is this not in the Prelude...?
    split :: Eq a => a -> [a] -> [[a]]
    split _ [] = []
    split d s = x : split d (drop 1 y)
      where (x, y) = span (/= d) s

data KlisterPathError
  = ModuleNotFound String FilePath KlisterPath
  | TooManyFound String [FilePath]
  | TooManyFoundInStdlib String [FilePath]
  deriving (Show)

ppKlisterPathError :: KlisterPathError -> PP.Doc ann
ppKlisterPathError =
  \case
    ModuleNotFound modName parentDir (KlisterPath kPath) ->
      PP.vsep $
        [ PP.pretty $ "Module not found: " <> modName
        , PP.pretty $ "Searched in directory at " <> parentDir
        , PP.pretty $ "And on $KLISTERPATH:"
        , PP.vsep $ map PP.pretty $ Set.toList $ kPath
        ]
    TooManyFound modName found ->
      PP.vsep $
        [ PP.pretty $
            "Ambiguous module name: " <> modName
        , PP.pretty "Candidates:"
        , PP.vsep $ map PP.pretty found
        ]
    TooManyFoundInStdlib modName found ->
      PP.vsep $
        [ PP.pretty $
            "Internal error; ambiguous module in stdlib:" <> modName
        , PP.pretty "Candidates:"
        , PP.vsep $ map PP.pretty found
        ]

findInDirectory :: String -> FilePath -> IO [FilePath]
findInDirectory moduleName dir =
  map (dir </>) . filter (== moduleName) <$> listDirectory dir

findInKlisterPath ::
  KlisterPath {- ^ Path to search -} ->
  String {- ^ Module to find -} ->
  IO [FilePath] {- ^ Candidates found -}
findInKlisterPath (KlisterPath paths) moduleName =
  concat <$> mapM (findInDirectory moduleName) (Set.toList paths)

stdlibPath :: IO String
stdlibPath = getDataDir <&> (</> "stdlib")

findInStdlib ::
  String {- ^ Module to find -} ->
  IO [FilePath]
findInStdlib moduleName = findInDirectory moduleName =<< stdlibPath

-- | Search for a module on the filesystem.
--
-- See the module comment in "KlisterPath" for an overview of the search
-- procedure.
findModule ::
  KlisterPath {- ^ Path to search -} ->
  SrcLoc {- ^ Location of import form -} ->
  String {- ^ Module name -} ->
  IO (Either KlisterPathError ModuleName)
findModule kPath loc moduleName = do
  let srcDir = takeDirectory (view srcLocFilePath loc)
  inSameDir <- findInDirectory moduleName srcDir
  inStdlib <- findInStdlib moduleName
  onKPath <- findInKlisterPath kPath moduleName
  case (inSameDir, inStdlib, onKPath) of
    ([path], _, _) -> Right <$> moduleNameFromPath path
    ([], [path], _) -> Right <$> moduleNameFromPath path
    ([], [], [path]) -> Right <$> moduleNameFromPath path
    ([], [], []) -> pure (Left (ModuleNotFound moduleName srcDir kPath))
    ([], [], paths) -> pure (Left (TooManyFound moduleName paths))
    ([], paths, _) -> pure (Left (TooManyFoundInStdlib moduleName paths))
    (paths, _, _) -> pure (Left (TooManyFound moduleName paths))
