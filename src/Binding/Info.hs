{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
module Binding.Info where

import Data.Data (Data)

data BindingInfo loc
  = BoundLocally loc
  | Defined loc
  -- TODO add the binding info of the exported name to Imported, to
  -- enable go to definition
  | Imported loc
  deriving (Data, Eq, Functor, Show)
