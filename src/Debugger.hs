{-# LANGUAGE  DerivingStrategies         #-}
{-# LANGUAGE  FlexibleInstances          #-}
{-# LANGUAGE  FunctionalDependencies     #-}
{-# LANGUAGE  ScopedTypeVariables        #-}
{-# LANGUAGE  UndecidableInstances       #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Debugger
-- Copyright   :  (c) Jeffrey M. Young
--                    Samuel Gélineau
--                    David Thrane Christiansen
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Jeffrey Young      <jeffrey.young@iohk.io>
--                Samuel Gélineau    <gelisam@gmail.com>
--                David Christiansen <david@davidchristiansen.dk>
-- Stability   :  experimental
--
-- A Common Lisp style Debugger for klister.
-----------------------------------------------------------------------------


module Debugger where
  -- DYG explicit export list

import Evaluator

import Data.Bifunctor
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader (ReaderT)
import qualified Control.Monad.Trans.State.Lazy   as LazyState
import qualified Control.Monad.Trans.State.Strict as StrictState
import qualified Control.Monad.Trans.Reader as Reader
-- -----------------------------------------------------------------------------
-- Types


-- conceptually this is a ReaderT (DebugContext e) (ExceptT e) IO a but I've
-- just fused the transformers to have more control over the monad instance
newtype Debug r e a = Debug { runDebug :: r -> IO (Either e a) }

debugRun :: r -> Debug r e a -> IO (Either e a)
debugRun = flip runDebug

{-# INLINE mapDebug #-}
mapDebug :: (a -> b) -> Debug r e a -> Debug r e b
mapDebug f = Debug . fmap (fmap (second f)) . runDebug

withDebug :: (r' -> r) -> Debug r e a -> Debug r' e a
withDebug f m = Debug $ runDebug m . f

debugBy :: (e -> e') -> Debug r e a -> Debug r e' a
debugBy f = Debug . fmap go . runDebug
  where
    go g = do
      g' <- g
      return $
        case g' of
          Left e -> Left (f e)
          Right r -> Right r

ask' :: Debug r e r
ask' = Debug $ \r -> return $ Right r

instance Functor (Debug r e) where
  fmap = mapDebug

instance Applicative (Debug r e) where
  pure a  = Debug $ const (return (Right a))
  Debug f <*> Debug v = Debug $ \rr -> do
    mf <- f rr
    case mf of
      (Left fer) -> return (Left fer)
      (Right k)  -> do
        mv <- v rr
        case mv of
          (Left ver) -> return (Left ver)
          Right x    -> return (Right (k x))

instance Monad (Debug r e) where
  Debug m >>= f  = Debug $ \r -> do
    ma <- m r
    case ma of
      Left err  -> return (Left err)
      Right val -> fmap (debugRun r) f val

instance MonadIO (Debug r e) where
  liftIO = Debug . const . fmap Right

instance MonadDebugger e m => MonadDebugger e (ReaderT r m) where
  debug = lift . debug
  catch = Reader.liftCatch catch

instance MonadDebugger e m => MonadDebugger e (LazyState.StateT s m) where
  debug = lift . debug
  catch = LazyState.liftCatch catch

instance MonadDebugger e m => MonadDebugger e (StrictState.StateT s m) where
  debug = lift . debug
  catch = StrictState.liftCatch catch

-- | Type class that defines the interface for any debugger. Each instance is a
-- debugger in their own right
class (Monad io, MonadIO io) => MonadDebugger e io | io -> e where
  -- conceptually this is throw
  debug :: e -> io a
  -- conceptually this is catch with a handler
  catch :: io a -> (e -> io a) -> io a

-- | This debugger is the simplest debugger. It accepts no user inputs, instead
-- it only reports whatever stack trace its recorded.
instance MonadDebugger e (Debug DebugContext e) where
  debug e = Debug $ const (return (Left e))
  catch (Debug m) hndl  = Debug $ \r -> do
    a <- m r
    case a of
      Left e -> runDebug (hndl e) r
      v@Right{} -> return v

data DebugContext = NoContext
                  | DebugContext { _stackTrace :: EState }
                    deriving Show

initialContext :: DebugContext
initialContext = NoContext

-- checkError :: Debug e (Maybe e)
-- checkError = R.asks _currentError

-- DYG next:
-- - instead of projecting the error in debug invocations (see line 870 in Expander.Monad)
-- - we record the stack trace
-- - also merge catch and debug. In the debugger as envisioned these are the same things
-- - can we write a combinator that wraps a computation with a standard handler?
-- - I definitely believe we can, there are likely classes of handlers, with the simplest
-- - one being throwError that just reports the error.

-- -----------------------------------------------------------------------------
-- Top level API

-- enterDebugger :: ExpansionErr -> EState -> Debug Value
-- enterDebugger exp_err st =
