{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
module Binding.Info where

import Data.Data (Data)

import ShortShow

data BindingInfo loc
  = BoundLocally loc
  | Defined loc
  -- TODO add the binding info of the exported name to Imported, to
  -- enable go to definition
  | Imported loc
  deriving (Data, Eq, Functor, Show)

instance ShortShow loc => ShortShow (BindingInfo loc) where
  shortShow (BoundLocally l) = "BoundLocally " ++ shortShow l
  shortShow (Defined l) = "Defined " ++ shortShow l
  shortShow (Imported l) = "Imported " ++ shortShow l
