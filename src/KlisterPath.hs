{-
Module           : KlisterPath
Description      : Implementation of $KLISTERPATH
Copyright        : (c) Klister Collaborators 2020
License          : See GH#55
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module KlisterPath
  ( KlisterPath
  , KlisterPathError(..)
  , ppKlisterPathError
  , getKlisterPath
  , makeKlisterPath
  , importFromKlisterPath
  ) where

import Data.Functor ((<&>))
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Traversable (for)
import System.Directory (canonicalizePath, listDirectory)
import System.FilePath.Posix ((</>))
import System.Environment (lookupEnv)

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
  = ModuleNotFound String
  | TooManyFound String [FilePath]
  deriving (Eq, Show)

ppKlisterPathError :: KlisterPathError -> PP.Doc ann
ppKlisterPathError =
  \case
    ModuleNotFound modName ->
      PP.pretty $ "Module not found on $KLISTERPATH: " <> modName
    TooManyFound modName found ->
      PP.vsep $
        [ PP.pretty $
            "Ambiguous module name: " <> modName
        , PP.pretty "Candidates:"
        , PP.vsep $ map PP.pretty found
        ]

findInKlisterPath ::
  KlisterPath {- ^ Path to search -} ->
  String {- ^ Module to find -} ->
  IO (Set FilePath) {- ^ Candidates found -}
findInKlisterPath (KlisterPath paths) moduleName =
  Set.fromList . concat <$>
    (for (Set.toList paths) $ \path ->
      map (path </>) . filter (== moduleName) <$> listDirectory path)

importFromKlisterPath ::
  KlisterPath {- ^ Path to search -} ->
  String {- ^ Module to find -} ->
  IO (Either KlisterPathError FilePath)
importFromKlisterPath klisterPath moduleName =
  findInKlisterPath klisterPath moduleName <&> Set.toList <&>
    \case
      [found] -> Right found
      [] -> Left (ModuleNotFound moduleName)
      tooMany -> Left (TooManyFound moduleName tooMany)
