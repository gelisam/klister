{-|
Module           : Syntax
Description      : User-facing syntax of Klister

'Syntax' is the user-facing syntax for Klister. It can come from parsing Klister
code or from the expansion of user macros. It is transformed into Klister\'s
core language by the expander.
-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Syntax where

import Control.Lens hiding (List)
import Data.Data (Data)
import Data.Text (Text)
import qualified Data.Text as T

import Alpha
import ModuleName
import Phase
import Scope
import ScopeSet (ScopeSet)
import ShortShow
import qualified ScopeSet
import Signals (Signal)
import Syntax.SrcLoc

data Stx a = Stx
  { _stxScopeSet :: ScopeSet
  , _stxSrcLoc   :: !SrcLoc
  , _stxValue    :: a
  }
  deriving (Data, Eq, Functor, Show)
makeLenses ''Stx

data ExprF a
  = Id Text
  | String Text
  | Sig Signal
  | List [a]
  deriving (Data, Eq, Functor, Show)
makePrisms ''ExprF


newtype Syntax = Syntax { _unSyntax :: (Stx (ExprF Syntax)) }
  deriving (Data, Eq, Show)
makeLenses ''Syntax

type Ident = Stx Text

data ParsedModule a = ParsedModule
  { _moduleSource :: ModuleName
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
      mapRec (String str) = String str
      mapRec (Sig s) = Sig s
      mapRec (List xs) = List $ map (\stx -> mapScopes f stx) xs

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

flipScope' :: HasScopes a => a -> Scope -> a
flipScope' = adjustScope ScopeSet.flipUniversally

addScope' :: HasScopes a => a -> Scope -> a
addScope' = adjustScope ScopeSet.insertUniversally

removeScope' :: HasScopes a => a -> Scope -> a
removeScope' = adjustScope ScopeSet.deleteUniversally


addScopes :: HasScopes a => a -> ScopeSet -> a
addScopes a0 scopeSet
  = let a1 = addUniversalScopes a0 scopeSet
        a2 = addSpecificScopes a1 scopeSet
    in a2
  where
    addUniversalScopes :: HasScopes a => a -> ScopeSet -> a
    addUniversalScopes =
      foldlOf (to ScopeSet.contents . _1 . folded)
              addScope'

    addSpecificScopes :: HasScopes a => a -> ScopeSet -> a
    addSpecificScopes =
      ifoldlOf (to ScopeSet.contents .> _2 .> ifolded <. folded)
               addScope

stxLoc :: Syntax -> SrcLoc
stxLoc (Syntax (Stx _ srcloc _)) = srcloc

syntaxE :: Syntax -> ExprF Syntax
syntaxE (Syntax (Stx _ _ e)) = e

syntaxText :: Syntax -> Text
syntaxText (Syntax (Stx _ _ e)) = go e
  where
    go (Id x) = x
    go (String str) = T.pack $ show str
    go (Sig s) = T.pack (show s)
    go (List xs) = "(" <> T.intercalate " " (map syntaxText xs) <> ")"

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
  alphaCheck _ _ = notAlphaEquivalent

instance AlphaEq Syntax where
  alphaCheck (Syntax x1)
             (Syntax x2) = do
    alphaCheck x1 x2


instance ShortShow a => ShortShow (Stx a) where
  shortShow (Stx _ _ x) = shortShow x

instance ShortShow a => ShortShow (ExprF a) where
  shortShow (Id x) = shortShow x
  shortShow (String s) = show s
  shortShow (List xs) = shortShow xs
  shortShow (Sig s) = shortShow s

instance ShortShow Syntax where
  shortShow (Syntax x) = shortShow x

