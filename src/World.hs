{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module World where

import Control.Lens
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)

import Env
import Module
import Phase

data World a = World
  { _worldEnvironments :: !(Map Phase (Env a))
  , _worldModules :: !(Map ModuleName CompleteModule)
  , _worldVisited :: !(Map ModuleName (Set Phase))
  }
makeLenses ''World

phaseEnv :: Phase -> World a -> Env a
phaseEnv p = maybe Env.empty id . view (worldEnvironments . at p)

initialWorld :: World a
initialWorld =
  World { _worldEnvironments = Map.empty
        , _worldModules = Map.empty
        , _worldVisited = Map.empty
        }

addExpandedModule :: CompleteModule -> World a -> World a
addExpandedModule m =
  over (worldModules . at (view moduleName m))
  \case
    Nothing -> Just m
    Just m' -> Just m'


