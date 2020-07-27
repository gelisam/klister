{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
module Datatype where

import Control.Lens
import Data.String
import Data.Text (Text)

import Alpha
import Kind
import ModuleName
import ShortShow

newtype DatatypeName = DatatypeName { _datatypeNameText :: Text }
  deriving (Eq, IsString, Ord, Show)
makeLenses ''DatatypeName

data Datatype
  = Datatype
    { _datatypeModule :: !ModuleName -- ^ The module that defines the datatype
    , _datatypeName :: !DatatypeName -- ^ The unique name for the datatype at this module and phase
    }
  deriving (Eq, Ord, Show)
makeLenses ''Datatype

newtype ConstructorName = ConstructorName  { _constructorNameText :: Text }
  deriving (Eq, IsString, Ord, Show)
makeLenses ''ConstructorName

data Constructor
  = Constructor
    { _constructorModule :: !ModuleName -- ^ The module that defines the constructor
    , _constructorName :: !ConstructorName -- ^ The unique name for the constructor at this module and phase
    }
  deriving (Eq, Ord, Show)
makeLenses ''Constructor

instance ShortShow Constructor where
  shortShow = show

instance AlphaEq Constructor where
  alphaCheck c1 c2
    | c1 == c2 = pure ()
    | otherwise = notAlphaEquivalent

data DatatypeInfo
  = DatatypeInfo
    { _datatypeArgKinds :: [Kind]
    , _datatypeConstructors :: ![Constructor]
    }
  deriving (Eq)
makeLenses ''DatatypeInfo

data ConstructorInfo t
  = ConstructorInfo
    { _ctorArguments :: ![t] -- ^ Either a type parameter or a concrete type
    , _ctorDatatype :: !Datatype
    }
  deriving Eq
makeLenses ''ConstructorInfo
