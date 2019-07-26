{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | Utilities for analyzing the form of syntax in the expander monad
module Expander.Syntax where

import Control.Monad.Except
import Data.Text (Text)
import qualified Data.Text as T

import Expander.Monad
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

mustBeList :: Syntax -> Expand (Stx [Syntax])
mustBeList (Syntax (Stx scs srcloc (List xs))) = return (Stx scs srcloc xs)
mustBeList other = throwError (NotList other)

mustBeString :: Syntax -> Expand (Stx Text)
mustBeString (Syntax (Stx scs srcloc (String s))) = return (Stx scs srcloc s)
mustBeString other = throwError (NotString other)

mustBeModName :: Syntax -> Expand (Stx ModuleName)
mustBeModName (Syntax (Stx scs srcloc (String s))) =
  Stx scs srcloc <$> liftIO (moduleNameFromLocatedPath srcloc (T.unpack s))
-- TODO use hygiene here instead
mustBeModName (Syntax (Stx scs srcloc (Id "kernel"))) =
  return (Stx scs srcloc (KernelName kernelName))
mustBeModName other = throwError (NotModName other)

class MustBeVec a where
  mustBeVec :: Syntax -> Expand (Stx a)

instance MustBeVec () where
  mustBeVec (Syntax (Stx scs srcloc (Vec []))) = return (Stx scs srcloc ())
  mustBeVec other = throwError (NotRightLength 0 other)

instance MustBeVec Syntax where
  mustBeVec (Syntax (Stx scs srcloc (Vec [x]))) = return (Stx scs srcloc x)
  mustBeVec other = throwError (NotRightLength 1 other)

instance MustBeVec (Syntax, Syntax) where
  mustBeVec (Syntax (Stx scs srcloc (Vec [x, y]))) = return (Stx scs srcloc (x, y))
  mustBeVec other = throwError (NotRightLength 2 other)

instance (a ~ Syntax, b ~ Syntax, c ~ Syntax) => MustBeVec (a, b, c) where
  mustBeVec (Syntax (Stx scs srcloc (Vec [x, y, z]))) = return (Stx scs srcloc (x, y, z))
  mustBeVec other = throwError (NotRightLength 3 other)

instance MustBeVec (Syntax, Syntax, Syntax, Syntax) where
  mustBeVec (Syntax (Stx scs srcloc (Vec [w, x, y, z]))) = return (Stx scs srcloc (w, x, y, z))
  mustBeVec other = throwError (NotRightLength 4 other)

instance MustBeVec (Syntax, Syntax, Syntax, Syntax, Syntax) where
  mustBeVec (Syntax (Stx scs srcloc (Vec [v, w, x, y, z]))) =
    return (Stx scs srcloc (v, w, x, y, z))
  mustBeVec other = throwError (NotRightLength 5 other)

instance MustBeVec [Syntax] where
  mustBeVec (Syntax (Stx scs srcloc (Vec xs))) =
    return (Stx scs srcloc xs)
  mustBeVec other = throwError (NotVec other)
