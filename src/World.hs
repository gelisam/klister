{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module World where

import Control.Lens
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Sequence as Seq
import Util.Set (Set)
import Data.Maybe (fromMaybe)

import Core (MacroVar, Var)
import Datatype
import Env
import CEKEvaluator (EvalResult)
import Module
import ModuleName
import Phase
import SplitType
import Type
import Type.Context

import Util.Store

data World a = World
  { _worldEnvironments :: !(Store Phase (Env Var a))
  , _worldTypeContexts :: !(TypeContext Var SchemePtr)
  , _worldTransformerEnvironments :: !(Store Phase (Env MacroVar a))
  , _worldModules      :: !(HashMap ModuleName CompleteModule)
  , _worldVisited      :: !(HashMap ModuleName (Set Phase))
  , _worldExports      :: !(HashMap ModuleName Exports)
  , _worldEvaluated    :: !(HashMap ModuleName (Seq EvalResult))
  , _worldDatatypes    :: !(Store Phase (HashMap Datatype DatatypeInfo))
  , _worldConstructors :: !(Store Phase (HashMap Constructor (ConstructorInfo Ty)))
  , _worldLocation     :: FilePath
  }
makeLenses ''World

phaseEnv :: Phase -> World a -> Env Var a
phaseEnv p = fromMaybe Env.empty . view (worldEnvironments . at p)

initialWorld :: FilePath -> World a
initialWorld fp =
  World { _worldEnvironments = mempty
        , _worldTypeContexts = mempty
        , _worldTransformerEnvironments = mempty
        , _worldModules      = HM.empty
        , _worldVisited      = HM.empty
        , _worldExports      = HM.empty
        , _worldEvaluated    = HM.empty
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
