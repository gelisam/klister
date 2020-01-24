{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Expander.Error where

import Control.Lens
import Numeric.Natural
import Data.Text (Text)
import qualified Data.Text as T

import Core
import Evaluator
import Expander.Task
import Phase
import Pretty

import ScopeCheck
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
  | NotExported Ident Phase
  | ReaderError Text
  | ScopeCheckError ScopeCheckError
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
  pp env (NotEmpty stx) =
    hang 2 $ group $ vsep [text "Expected (), but got", pp env stx]
  pp env (NotCons stx) =
    hang 2 $ group $ vsep [text "Expected non-empty parens, but got", pp env stx]
  pp env (NotList stx) =
    hang 2 $ group $ vsep [text "Expected parens, but got", pp env stx]
  pp env (NotString stx) =
    hang 2 $ group $
    vsep [ text "Expected string literal, but got"
         , pp env stx
         ]
  pp env (NotModName stx) =
    hang 2 $ group $
    vsep [ text "Expected module name (string or `kernel'), but got"
         , pp env stx
         ]
  pp env (NotRightLength len stx) =
    hang 2 $ group $
    vsep [ text "Expected" <+> viaShow len <+> text "entries between parentheses, but got"
         , pp env stx
         ]
  pp env (NotVec stx) =
    hang 2 $ group $ vsep [text "Expected square-bracketed vec but got", pp env stx]
  pp env (NotImportSpec stx) =
    hang 2 $ group $ vsep [text "Expected import spec but got", pp env stx]
  pp env (UnknownPattern stx) =
    hang 2 $ group $ vsep [text "Unknown pattern",  pp env stx]
  pp env (MacroRaisedSyntaxError err) =
    let locs = view syntaxErrorLocations err
        msg = text "Syntax error from macro:" <> line <>
              pp env (view syntaxErrorMessage err)
    in hang 4 $ group $
       case locs of
         [] -> msg
         (Syntax l : ls) ->
           pp env (view stxSrcLoc l) <> text ":" <> line <> msg <>
           case ls of
             [] -> mempty
             more -> text "Additional locations:" <> line <> vsep [pp env loc | Syntax (Stx _ loc _) <- more]
  pp env (MacroEvaluationError p err) =
    hang 4 $ group $ text "Error during macro evaluation at phase" <+> pp env p <>
    text ":" <> line <> text (evalErrorText err)
  pp env (ValueNotMacro val) =
    text "Not a macro monad value:" <+> pp env val
  pp env (ValueNotSyntax val) =
    hang 4 $ group $ text "Not a syntax object: " <> line <> pp env val
  pp _env (NoSuchFile filename) =
    text "User error; no such file: " <> string filename
  pp env (NotExported (Stx _ loc x) p) =
    group $ hang 4 $ vsep [ pp env loc <> text ":"
                          , text "Not available at phase" <+> pp env p <> text ":" <+> pp env x
                          ]
  pp _env (InternalError str) =
    text "Internal error during expansion! This is a bug in the implementation." <> line <> string str
  pp _env (ReaderError txt) =
    vsep (map text (T.lines txt))
  pp _env (ScopeCheckError txt) =
    vsep (map text (T.lines (T.pack (show txt)))) -- TODO better printing
