{-# LANGUAGE OverloadedStrings #-}
module Expander.Error where

import Numeric.Natural
import Data.Text (Text)
import qualified Data.Text as T

import Core
import Evaluator
import Expander.Task
import Phase
import Pretty
import ScopeSet
import ShortShow
import Syntax
import Value

data ExpansionErr
  = Ambiguous Phase Ident [ScopeSet]
  | Unknown (Stx Text)
  | NoProgress [ExpanderTask]
  | NotIdentifier Syntax
  | NotEmpty Syntax
  | NotCons Syntax
  | NotList Syntax
  | NotString Syntax
  | NotModName Syntax
  | NotRightLength Natural Syntax
  | NotVec Syntax
  | UnknownPattern Syntax
  | MacroRaisedSyntaxError (SyntaxError Syntax)
  | MacroEvaluationError Phase EvalError
  | ValueNotMacro Value
  | ValueNotSyntax Value
  | InternalError String
  deriving (Show)

expansionErrText :: ExpansionErr -> Text
expansionErrText (Ambiguous p x candidates) =
  "Ambiguous identifier in phase " <> T.pack (show p) <>
  " " <> T.pack (show x) <>
  T.concat ["\n\t" <> T.pack (show c) | c <- candidates]
expansionErrText (Unknown x) = "Unknown: " <> T.pack (show (pretty x))
expansionErrText (NoProgress tasks) =
  "No progress was possible:\n" <>
  T.concat (map (\x -> T.pack ("\t" ++ shortShow x ++ "\n")) tasks)
expansionErrText (NotIdentifier stx) =
  "Not an identifier: " <> syntaxText stx
expansionErrText (NotEmpty stx) = "Expected (), but got " <> syntaxText stx
expansionErrText (NotCons stx) =
  "Expected non-empty parens, but got " <> syntaxText stx
expansionErrText (NotList stx) =
  "Expected parens, but got " <> syntaxText stx
expansionErrText (NotString stx) =
  "Expected string literal, but got " <> syntaxText stx
expansionErrText (NotModName stx) =
  "Expected module name (string or `kernel'), but got " <> syntaxText stx
expansionErrText (NotRightLength len stx) =
  "Expected " <> T.pack (show len) <>
  " entries between square brackets, but got " <> syntaxText stx
expansionErrText (NotVec stx) =
  "Expected square-bracketed vec but got " <> syntaxText stx
expansionErrText (UnknownPattern stx) =
  "Unknown pattern " <> syntaxText stx
expansionErrText (MacroRaisedSyntaxError err) =
  "Syntax error from macro: " <> T.pack (show err)
expansionErrText (MacroEvaluationError p err) =
  "Error during macro evaluation at phase " <> T.pack (show (phaseNum p)) <>
  ": \n\t" <> evalErrorText err
expansionErrText (ValueNotMacro val) =
  "Not a macro monad value: " <> valueText val
expansionErrText (ValueNotSyntax val) =
  "Not a syntax object: " <> valueText val
expansionErrText (InternalError str) =
  "Internal error during expansion! This is a bug in the implementation." <> T.pack str
