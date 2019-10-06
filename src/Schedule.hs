{-# LANGUAGE TypeFamilies #-}

module Schedule
  ( Schedule(..)
  ) where

import           Data.Kind (Type)
import           Data.Functor.Identity

-- | Delay the current computation until the result from a subtask is available
class Schedule (f :: Type -> Type) where
  type Todo f :: Type -> Type
  schedule :: Todo f a -> f a

-- | You can schedule subtasks in the identity monad by just running them
instance Schedule Identity where
  type Todo Identity = Identity
  schedule = id
