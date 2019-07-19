{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Syntax where

import Control.Lens hiding (List)
import Control.Monad
import Data.Text (Text)
import qualified Data.Text as T

import Alpha
import Phase
import Scope
import ScopeSet (ScopeSet)
import ShortShow
import qualified ScopeSet
import Signals (Signal)


data SrcPos = SrcPos
  { _srcPosLine :: !Int
  , _srcPosCol  :: !Int
  }
  deriving (Eq, Show)
makeLenses ''SrcPos

data SrcLoc = SrcLoc
  { _srcLocFilePath :: !FilePath
  , _srcLocStart    :: !SrcPos
  , _srcLocEnd      :: !SrcPos
  }
  deriving (Eq, Show)
makeLenses ''SrcLoc

data Stx a = Stx
  { _stxScopeSet :: ScopeSet
  , _stxSrcLoc   :: !SrcLoc
  , _stxValue    :: a
  }
  deriving (Eq, Show)
makeLenses ''Stx

data ExprF a
  = Id Text
  | Sig Signal
  | Bool Bool
  | List [a]
  | Vec [a]
  deriving (Eq, Functor, Show)
makePrisms ''ExprF


newtype Syntax =
  Syntax (Stx (ExprF Syntax))
  deriving (Eq, Show)
makePrisms ''Syntax

type Ident = Stx Text

data ParsedModule a = ParsedModule
  { _moduleSource :: FilePath
  , _moduleLanguage :: a
  , _moduleContents :: a
  }
  deriving (Eq, Show)
makeLenses ''ParsedModule

class HasScopes a where
  getScopes :: a -> ScopeSet
  adjustScope :: (Scope -> ScopeSet -> ScopeSet) -> a -> Scope -> a
  mapScopes :: (ScopeSet -> ScopeSet) -> a -> a

instance HasScopes (Stx Text) where
  getScopes (Stx scs _ _) = scs
  adjustScope f (Stx scs srcloc x) sc = Stx (f sc scs) srcloc x
  mapScopes f (Stx scs srcloc x) = Stx (f scs) srcloc x

instance HasScopes Syntax where
  getScopes (Syntax (Stx scs _ _)) = scs
  adjustScope f stx sc = mapScopes (f sc) stx
  mapScopes f (Syntax (Stx scs srcloc e)) =
    Syntax $
    Stx (f scs) srcloc $
    mapRec e
    where
      mapRec (Id x) = Id x
      mapRec (Sig s) = Sig s
      mapRec (Bool b) = Bool b
      mapRec (List xs) = List $ map (\stx -> mapScopes f stx) xs
      mapRec (Vec xs) = Vec $ map (\stx -> mapScopes f stx) xs

instance Phased (Stx Text) where
  shift i = mapScopes (shift i)

instance Phased Syntax where
  shift i = mapScopes (shift i)


addScope :: HasScopes a => Phase -> a -> Scope -> a
addScope p = adjustScope (ScopeSet.insertAtPhase p)

removeScope :: HasScopes a => Phase -> a -> Scope -> a
removeScope p = adjustScope (ScopeSet.deleteAtPhase p)

flipScope :: HasScopes a => Phase -> a -> Scope -> a
flipScope p = adjustScope go
  where
    go sc scs
      | ScopeSet.member p sc scs = ScopeSet.deleteAtPhase p sc scs
      | otherwise                = ScopeSet.insertAtPhase p sc scs

addScope' :: HasScopes a => a -> Scope -> a
addScope' = adjustScope ScopeSet.insertUniversally


syntaxE :: Syntax -> ExprF Syntax
syntaxE (Syntax (Stx _ _ e)) = e

syntaxText :: Syntax -> Text
syntaxText (Syntax (Stx _ _ e)) = go e
  where
    go (Id x) = x
    go (Sig s) = T.pack (show s)
    go (Bool b) = if b then "#true" else "#false"
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


instance ShortShow a => ShortShow (Stx a) where
  shortShow (Stx _ _ x) = shortShow x

instance ShortShow a => ShortShow (ExprF a) where
  shortShow (Id x) = shortShow x
  shortShow (Bool b) = if b then "#true" else "#false"
  shortShow (List xs) = shortShow xs
  shortShow (Vec xs) = shortShow xs
  shortShow (Sig s) = shortShow s

instance ShortShow Syntax where
  shortShow (Syntax x) = shortShow x

