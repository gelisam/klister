{-# LANGUAGE RankNTypes #-}
-- |
-- Variants of (^.), (%=) and (.=) for pieces of state which are
-- represented using a Reader over an IORef instead of a State.
module Control.Lens.IORef where

import Control.Lens
import Control.Monad.IO.Class
import Control.Monad.Reader
import Data.IORef


viewIORef :: (MonadIO m, MonadReader r m)
          => Getting (IORef s) r (IORef s)  -- ^ Getter r (IORef s)
          -> Getting a s a                  -- ^ Getter s a
          -> m a
viewIORef refGetter leafGetter = do
  ref <- view refGetter
  s <- liftIO $ readIORef ref
  pure (view leafGetter s)

overIORef :: (MonadIO m, MonadReader r m)
          => Getting (IORef s) r (IORef s)  -- ^ Getter r (IORef s)
          -> ASetter' s a                   -- ^ Setter s a
          -> (a -> a)
          -> m ()
overIORef refGetter leafSetter f = do
  ref <- view refGetter
  liftIO $ modifyIORef ref (over leafSetter f)

setIORef :: (MonadIO m, MonadReader r m)
         => Getting (IORef s) r (IORef s)  -- ^ Getter r (IORef s)
         -> ASetter' s a                   -- ^ Setter s a
         -> a
         -> m ()
setIORef refGetter leafSetter a = do
  ref <- view refGetter
  liftIO $ modifyIORef ref (set leafSetter a)

-- | Operator variant of 'viewIORef'
(!^.) :: (MonadIO m, MonadReader r m)
      => Getting (IORef s) r (IORef s)  -- ^ Getter r (IORef s)
      -> Getting a s a                  -- ^ Getter s a
      -> m a
refGetter !^. leafSetter = viewIORef refGetter leafSetter
infixl 8 !^.

-- | Operator variant of 'overIORef'
(!%=) :: (MonadIO m, MonadReader r m)
      => ( Getting (IORef s) r (IORef s)
         , ASetter' s a
         )  -- ^ (Getter r (IORef s), Setter s a)
      -> (a -> a)
      -> m ()
(refGetter, leafSetter) !%= f = overIORef refGetter leafSetter f
infix 4 !%=

-- | Operator variant of 'setIORef'
(!.=) :: (MonadIO m, MonadReader r m)
      => ( Getting (IORef s) r (IORef s)
         , ASetter' s a
         )  -- ^ (Getter r (IORef s), Setter s a)
      -> a
      -> m ()
(refGetter, leafSetter) !.= a = setIORef refGetter leafSetter a
infix 4 !.=
