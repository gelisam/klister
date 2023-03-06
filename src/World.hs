{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module World where

import Control.Lens
import Data.Map (Map)
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
  , _worldModules      :: !(Map ModuleName CompleteModule)
  , _worldVisited      :: !(Map ModuleName (Set Phase))
  , _worldExports      :: !(Map ModuleName Exports)
  , _worldEvaluated    :: !(Map ModuleName [EvalResult])
  , _worldDatatypes    :: !(Map Phase (Map Datatype DatatypeInfo))
  , _worldConstructors :: !(Map Phase (Map Constructor (ConstructorInfo Ty)))
  , _worldLocation     :: FilePath
  }
makeLenses ''World

phaseEnv :: Phase -> World a -> Env Var a
phaseEnv p = maybe Env.empty id . view (worldEnvironments . at p)

initialWorld :: FilePath -> World a
initialWorld fp =
  World { _worldEnvironments = mempty
        , _worldTypeContexts = mempty
        , _worldTransformerEnvironments = mempty
        , _worldModules      = mempty
        , _worldVisited      = mempty
        , _worldExports      = mempty
        , _worldEvaluated    = mempty
        , _worldDatatypes    = mempty
        , _worldConstructors = mempty
        , _worldLocation     = fp
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
