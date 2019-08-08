module Expander.DeclScope where

import Data.Unique

newtype DeclValidityPtr = DeclValidityPtr Unique
  deriving (Eq, Ord)

instance Show DeclValidityPtr where
  show (DeclValidityPtr u) = "(DeclValidityPtr " ++ show (hashUnique u) ++ ")"

