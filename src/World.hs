{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module World where

import Control.Lens
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)

import Core (MacroVar, Var)
import Env
import Module
import ModuleName
import Phase

data World a = World
  { _worldEnvironments :: !(Map Phase (Env Var a))
  , _worldTransformerEnvironments :: !(Map Phase (Env MacroVar a))
  , _worldModules :: !(Map ModuleName CompleteModule)
  , _worldVisited :: !(Map ModuleName (Set Phase))
  , _worldExports :: !(Map ModuleName Exports)
  }
makeLenses ''World

phaseEnv :: Phase -> World a -> Env Var a
phaseEnv p = maybe Env.empty id . view (worldEnvironments . at p)

initialWorld :: World a
initialWorld =
  World { _worldEnvironments = Map.empty
        , _worldTransformerEnvironments = Map.empty
        , _worldModules = Map.empty
        , _worldVisited = Map.empty
        , _worldExports = Map.empty
        }

addExpandedModule :: CompleteModule -> World a -> World a
addExpandedModule m =
  over (worldModules . at (getName m))
  \case
    Nothing -> Just m
    Just m' -> Just m'
  where
    getName :: CompleteModule -> ModuleName
    getName (Expanded em _) = view moduleName em
    getName (KernelModule _) = KernelName kernelName


