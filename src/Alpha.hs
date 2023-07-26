{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
module Alpha where

import Control.Applicative
import Control.Lens
import Control.Monad
import Control.Monad.State
import Data.IntMap.Strict (IntMap)
import Data.Maybe
import Data.Text

import Unique

import Util.Key


data AlphaState = AlphaState
  { _alphaStateEnv1 :: IntMap Int
  , _alphaStateEnv2 :: IntMap Int
  , _alphaStateNext :: Int
  }
makeLenses ''AlphaState

initialAlphaState :: AlphaState
initialAlphaState = AlphaState
  { _alphaStateEnv1 = mempty
  , _alphaStateEnv2 = mempty
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
    maybeM <- use (alphaStateEnv1 . at (getKey x))
    maybeN <- use (alphaStateEnv2 . at (getKey y))
    guard (maybeM == maybeN)
    when (isNothing maybeM) $ do
      n <- unAlpha nextInt
      assign (alphaStateEnv1 . at (getKey x)) (Just n)
      assign (alphaStateEnv2 . at (getKey y)) (Just n)

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
