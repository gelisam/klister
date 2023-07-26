{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SplitType where

import Control.Lens hiding (children)
import Control.Monad.Writer

import PartialType
import Type
import Unique

import Util.Store (Store)
import qualified Util.Store as S
import Util.Key

newtype SplitTypePtr = SplitTypePtr Unique
  deriving newtype (Eq, Ord, HasKey)

instance Show SplitTypePtr where
  show (SplitTypePtr i) = "(SplitTypePtr " ++ show (hashUnique i) ++ ")"

newSplitTypePtr :: IO SplitTypePtr
newSplitTypePtr = SplitTypePtr <$> newUnique

data SplitType = SplitType
  { _splitTypeRoot :: SplitTypePtr
  , _splitTypeDescendants :: Store SplitTypePtr (TyF SplitTypePtr)
  }
makeLenses ''SplitType

unsplitType :: SplitType -> PartialType
unsplitType t = PartialType $ go (view splitTypeRoot t)
  where
    go :: SplitTypePtr -> Maybe (TyF PartialType)
    go ptr = do
      this <- view (splitTypeDescendants . at ptr) t
      return (fmap (PartialType . go) this)

splitType :: PartialType -> IO SplitType
splitType partialType = do
  root <- newSplitTypePtr
  ((), childMap) <- runWriterT $ go root (unPartialType partialType)
  return $ SplitType root childMap
  where
    go ::
      SplitTypePtr -> Maybe (TyF PartialType) ->
      WriterT (Store SplitTypePtr (TyF SplitTypePtr)) IO ()
    go _ Nothing = pure ()
    go place (Just t) = do
      children <- flip traverse t $ \p -> do
        here <- liftIO newSplitTypePtr
        go here (unPartialType p)
        pure here
      tell $ S.singleton place children

newtype SchemePtr = SchemePtr Unique deriving newtype (Eq, Ord, HasKey)

newSchemePtr :: IO SchemePtr
newSchemePtr = SchemePtr <$> newUnique

instance Show SchemePtr where
  show (SchemePtr ptr) =  "(SchemePtr " ++ show (hashUnique ptr) ++ ")"
