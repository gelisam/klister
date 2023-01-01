{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Utilities for analyzing the form of syntax in the expander monad
module Expander.Syntax where

import Control.Monad.Except
import Data.List (nub, sort)
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural

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

mustBeInteger :: Syntax -> Expand (Stx Integer)
mustBeInteger (Syntax (Stx scs srcloc (Integer n))) = return (Stx scs srcloc n)
mustBeInteger other = throwError (NotInteger other)

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


mustHaveEntries
  :: ( FixedLengthList item r
     , item ~ Syntax
     )
  => Syntax -> Expand (Stx r)
mustHaveEntries stx@(Syntax (Stx scs srcloc (List xs))) = do
  case checkLength xs of
    Right r -> do
      pure (Stx scs srcloc r)
    Left lengths -> do
      throwError (NotRightLength lengths stx)
mustHaveEntries other = do
  throwError (NotList other)

class FixedLengthList item r where
  checkLength :: [item] -> Either [Natural] r

instance ( FixedLengthList e1 a
         , FixedLengthList e2 b
         , e1 ~ e2
         ) => FixedLengthList e1 (Either a b)
         where
  checkLength xs
    = case (checkLength xs, checkLength xs) of
        (Right a, _)
          -> pure (Left a)
        (_, Right b)
          -> pure (Right b)
        (Left lengths1, Left lengths2)
          -> Left $ nub $ sort (lengths1 ++ lengths2)

instance FixedLengthList item () where
  checkLength []
    = pure ()
  checkLength _
    = Left [0]

instance item ~ Syntax => FixedLengthList item Syntax where
  checkLength [x]
    = pure x
  checkLength _
    = Left [1]

instance (a ~ item, b ~ item) => FixedLengthList item (a, b) where
  checkLength [x, y]
    = return (x, y)
  checkLength _
    = Left [2]

instance (a ~ item, b ~ item, c ~ item) => FixedLengthList item (a, b, c) where
  checkLength [x, y, z]
    = pure (x, y, z)
  checkLength _
    = Left [3]

instance (a ~ item, b ~ item, c ~ item, d ~ item) => FixedLengthList item (a, b, c, d) where
  checkLength [w, x, y, z]
    = pure (w, x, y, z)
  checkLength _
    = Left [4]

instance (a ~ item, b ~ item, c ~ item, d ~ item, e ~ item) => FixedLengthList item (a, b, c, d, e) where
  checkLength [v, w, x, y, z]
    = pure (v, w, x, y, z)
  checkLength _
    = Left [5]


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
