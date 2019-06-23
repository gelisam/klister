{-# LANGUAGE DeriveFunctor, OverloadedStrings #-}
module Syntax where

import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T

data SrcPos = SrcPos !Int !Int
  deriving (Eq, Show)

data SrcLoc = SrcLoc !FilePath !SrcPos !SrcPos
  deriving (Eq, Show)

-- Int should be enough for now - consider bumping to something like int64
newtype Scope = Scope Int
  deriving (Eq, Ord, Show)

nextScope :: Scope -> Scope
nextScope (Scope i) = Scope (i + 1)

type ScopeSet = Set.Set Scope

noScopes :: ScopeSet
noScopes = Set.empty


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
addScope = adjustScope Set.insert

removeScope :: Syntax -> Scope -> Syntax
removeScope = adjustScope Set.delete

flipScope :: Syntax -> Scope -> Syntax
flipScope = adjustScope flip
  where
    flip sc scs
      | Set.member sc scs = Set.delete sc scs
      | otherwise         = Set.insert sc scs


syntaxText :: Syntax -> Text
syntaxText (Syntax (Stx _ _ e)) = go e
  where
    go (Id x) = x
    go (List xs) = "(" <> T.intercalate " " (map syntaxText xs) <> ")"
    go (Vec xs) = "[" <> T.intercalate " " (map syntaxText xs) <> "]"

