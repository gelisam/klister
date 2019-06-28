{-# LANGUAGE DeriveFunctor, FlexibleInstances, OverloadedStrings, TemplateHaskell #-}
module Syntax where

import Control.Lens hiding (List)
import Control.Monad
import Data.Text (Text)
import qualified Data.Text as T

import Alpha
import Scope
import ScopeSet (ScopeSet)
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
  | List [a]
  | Vec [a]
  deriving (Eq, Functor, Show)
makePrisms ''ExprF


newtype Syntax =
  Syntax (Stx (ExprF Syntax))
  deriving (Eq, Show)
makePrisms ''Syntax

type Ident = Stx Text

class HasScopes a where
  getScopes :: a -> ScopeSet
  adjustScope :: (Scope -> ScopeSet -> ScopeSet) -> a -> Scope -> a

instance HasScopes (Stx Text) where
  getScopes (Stx scs _ _) = scs
  adjustScope f (Stx scs srcloc x) sc = Stx (f sc scs) srcloc x

instance HasScopes Syntax where
  getScopes (Syntax (Stx scs _ _)) = scs
  adjustScope f (Syntax (Stx scs srcloc e)) sc =
    Syntax $
    Stx (f sc scs) srcloc $
    adjustRec e
    where
      adjustRec (Id x) = Id x
      adjustRec (Sig s) = Sig s
      adjustRec (List xs) = List $ map (\stx -> adjustScope f stx sc) xs
      adjustRec (Vec xs) = Vec $ map (\stx -> adjustScope f stx sc) xs

addScope :: HasScopes a => a -> Scope -> a
addScope = adjustScope ScopeSet.insert

removeScope :: HasScopes a => a -> Scope -> a
removeScope = adjustScope ScopeSet.delete

flipScope :: Syntax -> Scope -> Syntax
flipScope = adjustScope go
  where
    go sc scs
      | ScopeSet.member sc scs = ScopeSet.delete sc scs
      | otherwise              = ScopeSet.insert sc scs


syntaxE :: Syntax -> ExprF Syntax
syntaxE (Syntax (Stx _ _ e)) = e

syntaxText :: Syntax -> Text
syntaxText (Syntax (Stx _ _ e)) = go e
  where
    go (Id x) = x
    go (Sig s) = T.pack (show s)
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
