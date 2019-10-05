{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}

module ScopeCheck
  ( MonadScopeCheck(..)
  , ScopeCheckError(..)
  , Todo(..)
  ) where

import Control.Lens
import Data.Kind (Type)
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import GHC.Generics (Generic)

import Core
import SplitCore
import Module
import Phase

class MonadScopeCheck (f :: Type -> Type) where
  throwScopeCheckError :: ScopeCheckError -> f a
  assertInContext :: Phase -> Var -> f ()

  -- | Like 'local'.
  extendVariableContext :: Var -> f a -> f a

  check :: Todo a -> f a

data Todo :: Type -> Type where
  TodoExpr :: SplitCorePtr -> Todo (CoreF SplitCorePtr)
  TodoDecl :: DeclPtr -> Todo (Decl DeclPtr SplitCorePtr)

data ScopeCheckError = ScopeCheckError ()

data VariableContext = VariableContext (Map Phase [Var])

type Ctx = Map Phase (Set Var)

data ScopeChecked a =
  ScopeChecked { checkedInCtx :: Ctx
               , checkedSubject :: a
               }
  deriving Functor

scopeCheck ::
  MonadScopeCheck f =>
  Module (ModuleBodyF ModBodyPtr) (Decl DeclPtr SplitCorePtr) ->
  f (ScopeChecked CompleteUserModule)
scopeCheck mod = do
  _

scopeCheckDecls ::
  MonadScopeCheck f =>
  ModuleBodyF ModBodyPtr (Decl DeclPtr SplitCorePtr) ->
  f (ScopeChecked [CompleteDecl])
scopeCheckDecls mod = _

scopeCheckDecl ::
  MonadScopeCheck f =>
  ModuleBodyF ModBodyPtr (Decl DeclPtr SplitCorePtr) ->
  f (ScopeChecked CompleteDecl)
scopeCheckDecl mod = _

scopeCheckCore ::
  MonadScopeCheck f =>
  ModuleBodyF ModBodyPtr (CoreF SplitCorePtr) ->
  f (ScopeChecked Core)
scopeCheckCore mod = _
