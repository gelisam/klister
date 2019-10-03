{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Expander.Error where

import Numeric.Natural
import Data.Text (Text)

import Core
import Evaluator
import Expander.Task
import Phase
import Pretty

import ScopeSet
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
  | NotImportSpec Syntax
  | UnknownPattern Syntax
  | MacroRaisedSyntaxError (SyntaxError Syntax)
  | MacroEvaluationError Phase EvalError
  | ValueNotMacro Value
  | ValueNotSyntax Value
  | InternalError String
  | NoSuchFile String
  deriving (Show)

instance Pretty VarInfo ExpansionErr where
  pp env (Ambiguous p x candidates) =
    hang 4 $
      text "Ambiguous identifier in phase" <+> pp env p <+>
      pp env x <> line <>
      vsep [viaShow c | c <- candidates]
  pp env (Unknown x) = text "Unknown:" <+> pp env x
  pp env (NoProgress tasks) =
    hang 4 $
      text "No progress was possible:" <> line <>
      vsep (map (pp env) tasks)
  pp env (NotIdentifier stx) =
    text "Not an identifier:" <+> pp env stx
  pp env (NotEmpty stx) = text "Expected (), but got" <+> pp env stx
  pp env (NotCons stx) =
    text "Expected non-empty parens, but got" <+> pp env stx
  pp env (NotList stx) =
    text "Expected parens, but got" <+> pp env stx
  pp env (NotString stx) =
    text "Expected string literal, but got" <+> pp env stx
  pp env (NotModName stx) =
    text "Expected module name (string or `kernel'), but got" <+> pp env stx
  pp env (NotRightLength len stx) =
    text "Expected" <+> viaShow len <+>
    text "entries between square brackets, but got" <+> pp env stx
  pp env (NotVec stx) =
    text "Expected square-bracketed vec but got" <+> pp env stx
  pp env (NotImportSpec stx) =
    text "Expected import spec but got" <+> pp env stx
  pp env (UnknownPattern stx) =
    text "Unknown pattern" <+> pp env stx
  pp _env (MacroRaisedSyntaxError err) =
    hang 4 $ group $ text "Syntax error from macro:" <> line <> viaShow err
  pp env (MacroEvaluationError p err) =
    hang 4 $ group $ text "Error during macro evaluation at phase" <+> pp env p <>
    text ":" <> line <> text (evalErrorText err)
  pp env (ValueNotMacro val) =
    text "Not a macro monad value:" <+> pp env val
  pp env (ValueNotSyntax val) =
    hang 4 $ group $ text "Not a syntax object: " <> line <> pp env val
  pp _env (NoSuchFile filename) =
    text "User error; no such file: " <> string filename
  pp _env (InternalError str) =
    text "Internal error during expansion! This is a bug in the implementation." <> line <> string str
