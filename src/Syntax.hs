{-|
Module           : Syntax
Description      : User-facing syntax of Klister

'Syntax' is the user-facing syntax for Klister. It can come from parsing Klister
code or from the expansion of user macros. It is transformed into Klister\'s
core language by the expander.
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Syntax
 ( addScope
 , removeScope
 , flipScope
 , flipScope'
 , addScope'
 , removeScope'
 , addScopes
 , stxLoc
 , syntaxE
 , syntaxText
 , module Syntax.Syntax
 )where

import Data.Text (Text)
import qualified Data.Text as T

import Phase
import Scope
import ScopeSet
import Syntax.SrcLoc
import Syntax.Syntax


addScope :: HasScopes a => Phase -> Scope -> a -> a
addScope p = adjustScope (ScopeSet.insertAtPhase p)

removeScope :: HasScopes a => Phase -> Scope -> a -> a
removeScope p = adjustScope (ScopeSet.deleteAtPhase p)

flipScope :: HasScopes a => Phase -> Scope -> a -> a
flipScope p = adjustScope go
  where
    go sc scs
      | ScopeSet.member p sc scs = ScopeSet.deleteAtPhase p sc scs
      | otherwise                = ScopeSet.insertAtPhase p sc scs

flipScope' :: HasScopes a => Scope -> a -> a
flipScope' = adjustScope ScopeSet.flipUniversally

addScope' :: HasScopes a => Scope -> a -> a
addScope' = adjustScope ScopeSet.insertUniversally

removeScope' :: HasScopes a => Scope -> a -> a
removeScope' = adjustScope ScopeSet.deleteUniversally

addScopes :: HasScopes p => ScopeSet -> p -> p
addScopes =  addScopes'

stxLoc :: Syntax -> SrcLoc
stxLoc (Syntax (Stx _ srcloc _)) = srcloc

syntaxE :: Syntax -> ExprF Syntax
syntaxE (Syntax (Stx _ _ e)) = e

syntaxText :: Syntax -> Text
syntaxText (Syntax (Stx _ _ e)) = go e
  where
    go (Id x) = x
    go (String str) = T.pack $ show str
    go (Integer s) = T.pack (show s)
    go (Int64 s) = T.pack (show s)
    go (Int32 s) = T.pack (show s)
    go (Int16 s) = T.pack (show s)
    go (Int8 s)  = T.pack (show s)
    go (Word64 s) = T.pack (show s)
    go (Word32 s) = T.pack (show s)
    go (Word16 s) = T.pack (show s)
    go (Word8 s)  = T.pack (show s)
    go (List xs) = "(" <> T.intercalate " " (map syntaxText xs) <> ")"
