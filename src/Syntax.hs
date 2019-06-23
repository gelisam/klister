{-# LANGUAGE DeriveFunctor, OverloadedStrings #-}
module Syntax where

import Data.Text (Text)
import qualified Data.Text as T

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

