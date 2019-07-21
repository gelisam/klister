{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module World where

import Control.Lens
import Control.Monad
import Control.Monad.Except
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import System.Directory

import Env
import Evaluator
import Expander
import Module
import Parser
import Phase
import Value

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

visit :: ModuleName -> World Value -> Expand (World Value)
visit name@(ModuleName file) world =
  do m <- case view (worldModules . at name) world of
            Just m -> return m
            Nothing ->
              do existsp <- liftIO $ doesFileExist file
                 when (not existsp) $
                   throwError $ InternalError $ "No such file: " ++ show file
                 stx <- liftIO (readModule file) >>=
                        \case
                          Left err -> throwError $ InternalError $ show err -- TODO
                          Right stx -> return stx
                 expandModule stx
     let world' = addExpandedModule m world
     p <- currentPhase
     let visitedp = Set.member p $
                    maybe Set.empty id $
                    view (worldVisited . at name) world'
     world'' <-
       if visitedp
         then return world'
         else
           do let i = phaseNum p
              let m' = shift i m
              (moreEnv, _) <- expandEval $ evalMod p m'
              return $
                over (worldVisited . at name) (Just . maybe (Set.singleton p) (Set.insert p)) $
                over worldEnvironments (Map.unionWith (<>) moreEnv) world'
     return world''


