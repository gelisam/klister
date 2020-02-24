{-# LANGUAGE TemplateHaskell #-}
module Datatype where

import Control.Lens
import Data.Text (Text)
import Numeric.Natural

import ModuleName
import Phase
import ShortShow

data Datatype
  = Datatype
    { _datatypeModule :: !ModuleName -- ^ The module that defines the datatype
    , _datatypePhase :: !Phase -- ^ The phase at which the datatype is valid
    , _datatypeName :: !Text -- ^ The unique name for the datatype at this module and phase
    }
  deriving (Eq, Ord, Show)
makeLenses ''Datatype

data Constructor
  = Constructor
    { _constructorModule :: !ModuleName -- ^ The module that defines the constructor
    , _constructorPhase :: !Phase -- ^ The phase at which the constructor is valid
    , _constructorName :: !Text -- ^ The unique name for the constructor at this module and phase
    }
  deriving (Eq, Ord, Show)
makeLenses ''Constructor

instance ShortShow Constructor where
  shortShow = show

data DatatypeInfo
  = DatatypeInfo
    { _datatypeArity :: !Natural -- ^ How many arguments does it take? (first-order version of a kind)
    , _datatypeConstructors :: ![Constructor]
    }
makeLenses ''DatatypeInfo

data ConstructorInfo t
  = ConstructorInfo
    { _ctorArguments :: ![Either Natural t] -- ^ Either a type parameter or a concrete type
    , _ctorDatatype :: !Datatype
    }
makeLenses ''ConstructorInfo
