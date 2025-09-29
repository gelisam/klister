{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}
module Datatype where

import Control.Lens
import Data.Data (Data)
import Data.String
import Data.Text (Text)
import Data.Hashable

import Alpha
import Kind
import ModuleName
import GHC.Generics (Generic)

newtype DatatypeName = DatatypeName { _datatypeNameText :: Text }
  deriving newtype (Eq, IsString, Ord, Show, Hashable)
  deriving stock Data
makeLenses ''DatatypeName

data Datatype
  = Datatype
    { _datatypeModule :: !ModuleName -- ^ The module that defines the datatype
    , _datatypeName :: !DatatypeName -- ^ The unique name for the datatype at this module and phase
    }
  deriving stock (Data, Eq, Ord, Show, Generic)
makeLenses ''Datatype

instance Hashable Datatype

newtype ConstructorName = ConstructorName  { _constructorNameText :: Text }
  deriving newtype (Eq, IsString, Ord, Show, Hashable)
  deriving stock   Data
makeLenses ''ConstructorName

data Constructor
  = Constructor
    { _constructorModule :: !ModuleName -- ^ The module that defines the constructor
    , _constructorName :: !ConstructorName -- ^ The unique name for the constructor at this module and phase
    }
  deriving (Data, Eq, Ord, Show, Generic)
makeLenses ''Constructor

instance Hashable Constructor

instance AlphaEq Constructor where
  alphaCheck c1 c2
    | c1 == c2 = pure ()
    | otherwise = notAlphaEquivalent

data DatatypeInfo
  = DatatypeInfo
    { _datatypeArgKinds :: [Kind]
    , _datatypeConstructors :: ![Constructor]
    }
  deriving Eq
makeLenses ''DatatypeInfo

data ConstructorInfo t
  = ConstructorInfo
    { _ctorArguments :: ![t] -- ^ Either a type parameter or a concrete type
    , _ctorDatatype :: !Datatype
    }
  deriving Eq
makeLenses ''ConstructorInfo
