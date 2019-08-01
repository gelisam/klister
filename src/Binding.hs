module Binding where

import Data.Unique

newtype Binding = Binding Unique
  deriving (Eq, Ord)

instance Show Binding where
  show (Binding b) = "(Binding " ++ show (hashUnique b) ++ ")"
