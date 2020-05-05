{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | Utilities for analyzing the form of syntax in the expander monad
module Expander.Syntax where

import Control.Monad.Except
import Data.Text (Text)
import qualified Data.Text as T

import Expander.Error
import Expander.Monad
import KlisterPath
import ModuleName
import Syntax


mustBeIdent :: Syntax -> Expand (Stx Text)
mustBeIdent (Syntax (Stx scs srcloc (Id x))) = return (Stx scs srcloc x)
mustBeIdent other = throwError (NotIdentifier other)

mustBeEmpty :: Syntax -> Expand (Stx ())
mustBeEmpty (Syntax (Stx scs srcloc (List []))) = return (Stx scs srcloc ())
mustBeEmpty other = throwError (NotEmpty other)

mustBeCons :: Syntax -> Expand (Stx (Syntax, [Syntax]))
mustBeCons (Syntax (Stx scs srcloc (List (x:xs)))) = return (Stx scs srcloc (x, xs))
mustBeCons other = throwError (NotCons other)

mustBeConsCons :: Syntax -> Expand (Stx (Syntax, Syntax, [Syntax]))
mustBeConsCons (Syntax (Stx scs srcloc (List (x:y:xs)))) = return (Stx scs srcloc (x, y, xs))
mustBeConsCons other = throwError (NotConsCons other)


mustBeList :: Syntax -> Expand (Stx [Syntax])
mustBeList (Syntax (Stx scs srcloc (List xs))) = return (Stx scs srcloc xs)
mustBeList other = throwError (NotList other)

mustBeString :: Syntax -> Expand (Stx Text)
mustBeString (Syntax (Stx scs srcloc (String s))) = return (Stx scs srcloc s)
mustBeString other = throwError (NotString other)

mustBeModName :: Syntax -> Expand (Stx ModuleName)
mustBeModName (Syntax (Stx scs srcloc (String s))) = do
  kPath <- klisterPath
  liftIO (findModule kPath srcloc (T.unpack s)) >>=
    \case
      Left err -> throwError (ImportError err)
      Right path -> pure $ Stx scs srcloc path
-- TODO use hygiene here instead
mustBeModName (Syntax (Stx scs srcloc (Id "kernel"))) =
  return (Stx scs srcloc (KernelName kernelName))
mustBeModName other = throwError (NotModName other)


class FixedLengthList a where
  mustHaveEntries :: Syntax -> Expand (Stx a)

instance FixedLengthList () where
  mustHaveEntries (Syntax (Stx scs srcloc (List []))) = return (Stx scs srcloc ())
  mustHaveEntries other = throwError (NotRightLength 0 other)

instance FixedLengthList Syntax where
  mustHaveEntries (Syntax (Stx scs srcloc (List [x]))) = return (Stx scs srcloc x)
  mustHaveEntries other = throwError (NotRightLength 1 other)

instance FixedLengthList (Syntax, Syntax) where
  mustHaveEntries (Syntax (Stx scs srcloc (List [x, y]))) = return (Stx scs srcloc (x, y))
  mustHaveEntries other = throwError (NotRightLength 2 other)

instance (a ~ Syntax, b ~ Syntax, c ~ Syntax) => FixedLengthList (a, b, c) where
  mustHaveEntries (Syntax (Stx scs srcloc (List [x, y, z]))) = return (Stx scs srcloc (x, y, z))
  mustHaveEntries other = throwError (NotRightLength 3 other)

instance FixedLengthList (Syntax, Syntax, Syntax, Syntax) where
  mustHaveEntries (Syntax (Stx scs srcloc (List [w, x, y, z]))) = return (Stx scs srcloc (w, x, y, z))
  mustHaveEntries other = throwError (NotRightLength 4 other)

instance FixedLengthList (Syntax, Syntax, Syntax, Syntax, Syntax) where
  mustHaveEntries (Syntax (Stx scs srcloc (List [v, w, x, y, z]))) =
    return (Stx scs srcloc (v, w, x, y, z))
  mustHaveEntries other = throwError (NotRightLength 5 other)

instance FixedLengthList [Syntax] where
  mustHaveEntries (Syntax (Stx scs srcloc (List xs))) =
    return (Stx scs srcloc xs)
  mustHaveEntries other = throwError (NotList other)


class MustHaveShape a where
  mustHaveShape :: Syntax -> Expand a

instance MustHaveShape Syntax where
  mustHaveShape = pure

instance MustHaveShape () where
  mustHaveShape (Syntax (Stx _ _ (List []))) = do
    pure ()
  mustHaveShape other@(Syntax (Stx _ _ (List (_:_)))) = do
    throwError (NotEmpty other)
  mustHaveShape other = throwError (NotList other)

instance ( MustHaveShape car
         , MustHaveShape cdr
         )
        => MustHaveShape (car, cdr) where
  mustHaveShape (Syntax (Stx scs srcloc (List (x:xs)))) = do
    car <- mustHaveShape x
    cdr <- mustHaveShape (Syntax (Stx scs srcloc (List xs)))
    pure (car, cdr)
  mustHaveShape other@(Syntax (Stx _ _ (List []))) = do
    throwError (NotCons other)
  mustHaveShape other = throwError (NotList other)

instance MustHaveShape a => MustHaveShape [a] where
  mustHaveShape (Syntax (Stx _ _ (List []))) = do
    pure []
  mustHaveShape (Syntax (Stx scs srcloc (List (x:xs)))) = do
    car <- mustHaveShape x
    cdr <- mustHaveShape (Syntax (Stx scs srcloc (List xs)))
    pure (car : cdr)
  mustHaveShape other = throwError (NotList other)
