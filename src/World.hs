{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module World where

import Control.Lens
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)

import Core (MacroVar, Var)
import Datatype
import Env
import Evaluator (EvalResult)
import Module
import ModuleName
import Phase
import SplitType
import Type
import Type.Context

data World a = World
  { _worldEnvironments :: !(Map Phase (Env Var a))
  , _worldTypeContexts :: !(TypeContext Var SchemePtr)
  , _worldTransformerEnvironments :: !(Map Phase (Env MacroVar a))
  , _worldModules :: !(Map ModuleName CompleteModule)
  , _worldVisited :: !(Map ModuleName (Set Phase))
  , _worldExports :: !(Map ModuleName Exports)
  , _worldEvaluated :: !(Map ModuleName [EvalResult])
  , _worldDatatypes :: !(Map Phase (Map Datatype DatatypeInfo))
  , _worldConstructors :: !(Map Phase (Map Constructor (ConstructorInfo Ty)))
  }
makeLenses ''World

phaseEnv :: Phase -> World a -> Env Var a
phaseEnv p = maybe Env.empty id . view (worldEnvironments . at p)

initialWorld :: World a
initialWorld =
  World { _worldEnvironments = Map.empty
        , _worldTypeContexts = mempty
        , _worldTransformerEnvironments = Map.empty
        , _worldModules = Map.empty
        , _worldVisited = Map.empty
        , _worldExports = Map.empty
        , _worldEvaluated = Map.empty
        , _worldDatatypes = Map.empty
        , _worldConstructors = Map.empty
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
