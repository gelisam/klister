{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Pretty.Renumber where

import Control.Lens
import Control.Monad.State

import Type
import Util.Store (Store)
import Util.Store qualified as Store
import Kind (KindVar)


newtype Renumbered = Renumbered
  { unRenumbered :: Int }

-- | The goal is to give a small, unique number to the few unification variables
-- which are present in a particular error message, in order to turn
--
-- > Infinite type detected: (MetaPtr 57868) = (List META(MetaPtr 57868))
--
-- into something more readable, like
--
-- > Infinite type detected: ?1 = (List ?1)
--
-- In order to do this, it is important to call 'renumber' _once_, on all the
-- unification variables in the error message, rather than calling 'renumber' on
-- separate components of the message and combining them.
renumber
  :: forall s t u
   . Traversal s t MetaPtr Renumbered
  -> Traversal t u KindVar Renumbered
  -> s -> u
renumber typeVars kindVars s = u
  where
  (t, n) = flip evalState Store.empty $ do
    t_ <- traverseOf typeVars renumberTypeVar s
    store <- get
    let n_ = Store.size store
    pure (t_, n_)
  u = flip evalState Store.empty $ do
    traverseOf kindVars renumberKindVar t

  renumberTypeVar :: MetaPtr -> State (Store MetaPtr Renumbered) Renumbered
  renumberTypeVar metaPtr = do
    store <- get
    case Store.lookup metaPtr store of
      Just renumbered -> do
        pure renumbered
      Nothing -> do
        let i = Store.size store
        let r = Renumbered i
        put $ Store.insert metaPtr r store
        pure r

  renumberKindVar :: KindVar -> State (Store KindVar Renumbered) Renumbered
  renumberKindVar kindVar = do
    store <- get
    case Store.lookup kindVar store of
      Just renumbered -> do
        pure renumbered
      Nothing -> do
        let i = n + Store.size store
        let r = Renumbered i
        put $ Store.insert kindVar r store
        pure r
