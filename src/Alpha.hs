{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
module Alpha where

import Control.Applicative
import Control.Lens
import Control.Monad.Fail
import Control.Monad.State
import Data.Map (Map)
import Data.Maybe
import Data.Text
import Data.Unique
import qualified Data.Map as Map


data AlphaState = AlphaState
  { _alphaStateEnv1 :: Map Unique Int
  , _alphaStateEnv2 :: Map Unique Int
  , _alphaStateNext :: Int
  }
makeLenses ''AlphaState

initialAlphaState :: AlphaState
initialAlphaState = AlphaState
  { _alphaStateEnv1 = Map.empty
  , _alphaStateEnv2 = Map.empty
  , _alphaStateNext = 0
  }


newtype Alpha a = Alpha
  { unAlpha :: StateT AlphaState Maybe a }
  deriving (Functor, Applicative, Alternative, Monad, MonadFail)

runAlpha :: Alpha a -> Maybe a
runAlpha = flip evalStateT initialAlphaState
         . unAlpha

nextInt :: Alpha Int
nextInt = Alpha $ do
  n <- use alphaStateNext
  modifying alphaStateNext (+1)
  pure n

notAlphaEquivalent :: Alpha a
notAlphaEquivalent = Alpha $ lift Nothing


class AlphaEq a where
  alphaCheck :: a -> a -> Alpha ()

alphaEq :: AlphaEq a
        => a -> a -> Bool
alphaEq x y = isJust $ runAlpha $ alphaCheck x y

instance AlphaEq Unique where
  alphaCheck x y = Alpha $ do
    maybeM <- use (alphaStateEnv1 . at x)
    maybeN <- use (alphaStateEnv2 . at y)
    guard (maybeM == maybeN)
    when (maybeM == Nothing) $ do
      n <- unAlpha nextInt
      assign (alphaStateEnv1 . at x) (Just n)
      assign (alphaStateEnv2 . at y) (Just n)

instance (AlphaEq a, AlphaEq b) => AlphaEq (a, b) where
  alphaCheck (x1, y1)
             (x2, y2) = do
    alphaCheck x1 x2
    alphaCheck y1 y2

instance AlphaEq a => AlphaEq [a] where
  alphaCheck []
             [] = do
    pure ()
  alphaCheck (x1:xs1)
             (x2:xs2) = do
    alphaCheck x1  x2
    alphaCheck xs1 xs2
  alphaCheck _ _ = notAlphaEquivalent

instance AlphaEq Text where
  alphaCheck x y = guard (x == y)
