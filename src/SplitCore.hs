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

module SplitCore where

import Control.Lens hiding (children)
import Control.Monad.Except
import Control.Monad.Writer
import Data.Map (Map)
import qualified Data.Map as Map

import Core
import PartialCore
import Unique

newtype SplitCorePtr = SplitCorePtr Unique
  deriving (Eq, Ord)

instance Show SplitCorePtr where
  show (SplitCorePtr u) = "(SplitCorePtr " ++ show (hashUnique u) ++ ")"

newSplitCorePtr :: IO SplitCorePtr
newSplitCorePtr = SplitCorePtr <$> newUnique

newtype PatternPtr = PatternPtr Unique
  deriving (Eq, Ord)

instance Show PatternPtr where
  show (PatternPtr u) = "(PatternPtr " ++ show (hashUnique u) ++ ")"

newPatternPtr :: IO PatternPtr
newPatternPtr = PatternPtr <$> newUnique

newtype TypePatternPtr = TypePatternPtr Unique
  deriving (Eq, Ord)

instance Show TypePatternPtr where
  show (TypePatternPtr u) = "(TypePatternPtr " ++ show (hashUnique u) ++ ")"

newTypePatternPtr :: IO TypePatternPtr
newTypePatternPtr = TypePatternPtr <$> newUnique


data SplitCore = SplitCore
  { _splitCoreRoot         :: SplitCorePtr
  , _splitCoreDescendants  :: Map SplitCorePtr (CoreF TypePatternPtr PatternPtr SplitCorePtr)
  , _splitCorePatterns     :: Map PatternPtr ConstructorPattern
  , _splitCoreTypePatterns :: Map TypePatternPtr TypePattern
  }
makeLenses ''SplitCore

unsplit :: SplitCore -> PartialCore
unsplit (SplitCore {..}) = PartialCore $ go _splitCoreRoot
  where
    go ::
      SplitCorePtr ->
      Maybe (CoreF (Maybe TypePattern) (Maybe ConstructorPattern) PartialCore)
    go ptr = do
      this <- Map.lookup ptr _splitCoreDescendants
      return (mapCoreF tpat pat (PartialCore . go) this)
    pat :: PatternPtr -> Maybe ConstructorPattern
    pat ptr = Map.lookup ptr _splitCorePatterns
    tpat :: TypePatternPtr -> Maybe TypePattern
    tpat ptr = Map.lookup ptr _splitCoreTypePatterns


split :: PartialCore -> IO SplitCore
split partialCore = do
  root <- newSplitCorePtr
  ((), (childMap, patMap, tpatMap)) <- runWriterT $ go root (unPartialCore partialCore)
  return $ SplitCore root childMap patMap tpatMap
  where
    go ::
      SplitCorePtr ->
      Maybe (CoreF (Maybe TypePattern) (Maybe ConstructorPattern) PartialCore) ->
      WriterT (Map SplitCorePtr (CoreF TypePatternPtr PatternPtr SplitCorePtr),
               Map PatternPtr ConstructorPattern,
               Map TypePatternPtr TypePattern)
        IO
        ()
    go _     Nothing = pure ()
    go place (Just c) = do
      children <- traverseCoreF tpat pat subtree c
      tell $ (Map.singleton place children, mempty, mempty)

    subtree p = do
      here <- liftIO newSplitCorePtr
      go here (unPartialCore p)
      pure here

    pat ::
      Maybe ConstructorPattern ->
      WriterT
        (Map SplitCorePtr (CoreF TypePatternPtr PatternPtr SplitCorePtr),
         Map PatternPtr ConstructorPattern,
         Map TypePatternPtr TypePattern)
        IO
        PatternPtr
    pat Nothing = liftIO newPatternPtr
    pat (Just it) = do
      here <- liftIO newPatternPtr
      tell (mempty, Map.singleton here it, mempty)
      return here

    tpat ::
      Maybe TypePattern ->
      WriterT
        (Map SplitCorePtr (CoreF TypePatternPtr PatternPtr SplitCorePtr),
         Map PatternPtr ConstructorPattern,
         Map TypePatternPtr TypePattern)
        IO
        TypePatternPtr
    tpat Nothing = liftIO newTypePatternPtr
    tpat (Just it) = do
      here <- liftIO newTypePatternPtr
      tell (mempty, mempty, Map.singleton here it)
      return here
