{-|
Module           : SplitCore
Description      : An intermediate datatype for partially expanded expressions.

'SplitCore' is a partially-constructed AST in which zero or more sub-trees may
be absent that's represented as an explicit pointer graph in the @Map@
component.

The expander uses 'SplitCore' while converting from 'Syntax' (what the user
types) to 'Core' (what the evaluator operates on). While the expander is
working, a given expression might have subtrees that have yet to be expanded
(for example, they might involve macros that are stalled waiting for some type
information). Such incomplete subexpressions are represented by 'SplitCorePtr',
which is essentially a unique identifier that will be looked up later, when
coalescing a 'SplitCore' expression into a fully-formed 'Core' expression.
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingStrategies #-}

module SplitCore where

import Prelude hiding (lookup)
import Control.Lens hiding (children)
import Control.Monad.Writer

import Core
import PartialCore
import Unique

import Util.Key
import Util.Store

newtype SplitCorePtr = SplitCorePtr Unique
  deriving newtype (Eq, Ord)

instance HasKey SplitCorePtr where
  getKey (SplitCorePtr u) = getKey u
  fromKey i = SplitCorePtr $! fromKey i
  {-# INLINE getKey  #-}
  {-# INLINE fromKey #-}

instance Show SplitCorePtr where
  show (SplitCorePtr u) = "(SplitCorePtr " ++ show (hashUnique u) ++ ")"

newSplitCorePtr :: IO SplitCorePtr
newSplitCorePtr = SplitCorePtr <$> newUnique

newtype PatternPtr = PatternPtr Unique
  deriving (Eq, Ord)

instance HasKey PatternPtr where
  getKey (PatternPtr u) = getKey u
  fromKey i = PatternPtr $! fromKey i
  {-# INLINE getKey  #-}
  {-# INLINE fromKey #-}

instance Show PatternPtr where
  show (PatternPtr u) = "(PatternPtr " ++ show (hashUnique u) ++ ")"

newPatternPtr :: IO PatternPtr
newPatternPtr = PatternPtr <$> newUnique

newtype TypePatternPtr = TypePatternPtr Unique
  deriving (Eq, Ord)

instance HasKey TypePatternPtr where
  getKey (TypePatternPtr u) = getKey u
  fromKey i = TypePatternPtr $! fromKey i
  {-# INLINE getKey  #-}
  {-# INLINE fromKey #-}

instance Show TypePatternPtr where
  show (TypePatternPtr u) = "(TypePatternPtr " ++ show (hashUnique u) ++ ")"

newTypePatternPtr :: IO TypePatternPtr
newTypePatternPtr = TypePatternPtr <$> newUnique

data SplitCore = SplitCore
  { _splitCoreRoot         :: SplitCorePtr
  , _splitCoreDescendants  :: Store SplitCorePtr (CoreF TypePatternPtr PatternPtr SplitCorePtr)
  , _splitCorePatterns     :: Store PatternPtr (ConstructorPatternF PatternPtr)
  , _splitCoreTypePatterns :: Store TypePatternPtr TypePattern
  }
makeLenses ''SplitCore

unsplit :: SplitCore -> PartialCore
unsplit (SplitCore {..}) = PartialCore $ go _splitCoreRoot
  where
    go ::
      SplitCorePtr ->
      Maybe (CoreF (Maybe TypePattern) PartialPattern PartialCore)
    go ptr = do
      this <- lookup ptr _splitCoreDescendants
      return (mapCoreF tpat pat (PartialCore . go) this)
    pat :: PatternPtr -> PartialPattern
    pat ptr = PartialPattern $ do
      this <- lookup ptr _splitCorePatterns
      return $ fmap pat this
    tpat :: TypePatternPtr -> Maybe TypePattern
    tpat ptr = lookup ptr _splitCoreTypePatterns


split :: PartialCore -> IO SplitCore
split partialCore = do
  root <- newSplitCorePtr
  ((), (childMap, patMap, tpatMap)) <- runWriterT $ go root (unPartialCore partialCore)
  return $ SplitCore root childMap patMap tpatMap
  where
    go ::
      SplitCorePtr ->
      Maybe (CoreF (Maybe TypePattern) PartialPattern PartialCore) ->
      WriterT (Store SplitCorePtr (CoreF TypePatternPtr PatternPtr SplitCorePtr),
               Store PatternPtr (ConstructorPatternF PatternPtr),
               Store TypePatternPtr TypePattern)
        IO
        ()
    go _     Nothing = pure ()
    go place (Just c) = do
      children <- traverseCoreF tpat pat subtree c
      tell (singleton place children, mempty, mempty)

    subtree p = do
      here <- liftIO newSplitCorePtr
      go here (unPartialCore p)
      pure here

    pat ::
      PartialPattern ->
      WriterT
        (Store SplitCorePtr (CoreF TypePatternPtr PatternPtr SplitCorePtr),
         Store PatternPtr (ConstructorPatternF PatternPtr),
         Store TypePatternPtr TypePattern)
        IO
        PatternPtr
    pat (PartialPattern Nothing) = liftIO newPatternPtr
    pat (PartialPattern (Just it)) = do
      here <- liftIO newPatternPtr
      layer <- traverse pat it
      tell (mempty, singleton here layer, mempty)
      return here

    tpat ::
      Maybe TypePattern ->
      WriterT
        (Store SplitCorePtr (CoreF TypePatternPtr PatternPtr SplitCorePtr),
         Store PatternPtr (ConstructorPatternF PatternPtr),
         Store TypePatternPtr TypePattern)
        IO
        TypePatternPtr
    tpat Nothing = liftIO newTypePatternPtr
    tpat (Just it) = do
      here <- liftIO newTypePatternPtr
      tell (mempty, mempty, singleton here it)
      return here
