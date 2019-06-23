{-# LANGUAGE DeriveFunctor, OverloadedStrings #-}
module Syntax where

import Control.Monad
import Data.Text (Text)
import qualified Data.Text as T

import Alpha
import Scope
import ScopeSet (ScopeSet)
import qualified ScopeSet


data SrcPos = SrcPos !Int !Int
  deriving (Eq, Show)

data SrcLoc = SrcLoc !FilePath !SrcPos !SrcPos
  deriving (Eq, Show)


data Stx a = Stx ScopeSet !SrcLoc a

data ExprF a
  = Id Text
  | List [a]
  | Vec [a]
  deriving Functor


newtype Syntax =
  Syntax (Stx (ExprF Syntax))

type Ident = Stx Text

adjustScope :: (Scope -> ScopeSet -> ScopeSet) -> Syntax -> Scope -> Syntax
adjustScope f (Syntax (Stx scs srcloc e)) sc =
  Syntax $
  Stx (f sc scs) srcloc $
  adjustRec e
  where
    adjustRec (Id x) = Id x
    adjustRec (List xs) = List $ map (\stx -> adjustScope f stx sc) xs
    adjustRec (Vec xs) = Vec $ map (\stx -> adjustScope f stx sc) xs

addScope :: Syntax -> Scope -> Syntax
addScope = adjustScope ScopeSet.insert

removeScope :: Syntax -> Scope -> Syntax
removeScope = adjustScope ScopeSet.delete

flipScope :: Syntax -> Scope -> Syntax
flipScope = adjustScope go
  where
    go sc scs
      | ScopeSet.member sc scs = ScopeSet.delete sc scs
      | otherwise              = ScopeSet.insert sc scs


syntaxText :: Syntax -> Text
syntaxText (Syntax (Stx _ _ e)) = go e
  where
    go (Id x) = x
    go (List xs) = "(" <> T.intercalate " " (map syntaxText xs) <> ")"
    go (Vec xs) = "[" <> T.intercalate " " (map syntaxText xs) <> "]"



instance AlphaEq SrcLoc where
  alphaCheck x y = guard (x == y)

instance AlphaEq a => AlphaEq (Stx a) where
  alphaCheck (Stx scopeSet1 srcLoc1 x1)
             (Stx scopeSet2 srcLoc2 x2) = do
    alphaCheck scopeSet1 scopeSet2
    alphaCheck srcLoc1   srcLoc2
    alphaCheck x1        x2

instance AlphaEq a => AlphaEq (ExprF a) where
  alphaCheck (Id x1)
             (Id x2) = do
    alphaCheck x1 x2
  alphaCheck (List xs1)
             (List xs2) = do
    alphaCheck xs1 xs2
  alphaCheck (Vec xs1)
             (Vec xs2) = do
    alphaCheck xs1 xs2
  alphaCheck _ _ = notAlphaEquivalent

instance AlphaEq Syntax where
  alphaCheck (Syntax x1)
             (Syntax x2) = do
    alphaCheck x1 x2
