{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings     #-}
module Expander.Error
  ( ExpansionErr(..)
  , SyntacticCategory(..)
  , TypeCheckError(..)
  , KindCheckError(..)
  , Tenon, tenon, Mortise, mortise
  , notRightLength
  ) where

import Control.Lens
import Numeric.Natural
import Data.Text (Text)
import Data.Sequence (Seq)
import qualified Data.Text as T
import Data.Foldable

import Core
import Datatype
import Evaluator
import Expander.Task
import Kind
import KlisterPath
import ModuleName
import Phase
import Pretty
import ScopeSet
import Syntax
import Syntax.SrcLoc
import Type
import Value

data ExpansionErr
  = Ambiguous Phase Ident (Seq ScopeSet)
  | Unknown (Stx Text)
  | NoProgress [ExpanderTask]
  | NotIdentifier Syntax
  | NotEmpty Syntax
  | NotCons Syntax
  | NotConsCons Syntax
  | NotList Syntax
  | NotInteger Syntax
  | NotString Syntax
  | NotModName Syntax
  | NotRightLength [Natural] Syntax
  | NotVec Syntax
  | NotImportSpec Syntax
  | NotExportSpec Syntax
  | UnknownPattern Syntax
  | MacroRaisedSyntaxError (SyntaxError Syntax)
  | MacroEvaluationError Phase EvalError
  | ValueNotMacro Value
  | ValueNotSyntax Value
  | ImportError KlisterPathError
  | InternalError String
  | NoSuchFile String
  | NotExported Ident Phase
  | ReaderError Text
  | WrongSyntacticCategory Syntax
      (Tenon SyntacticCategory)
      (Mortise SyntacticCategory)
  | NotValidType Syntax
  | TypeCheckError TypeCheckError
  | KindCheckError KindCheckError
  | WrongArgCount Syntax Constructor Int Int
  | NotAConstructor Syntax
  | WrongTypeArity Syntax TypeConstructor Natural Int
  | CircularImports ModuleName [ModuleName]
  deriving (Show)

-- | A newtype to add a type level witness that differentiates between a
-- @Mortise@ (a hole in woodworking) and a @Tenon@ tongue that fill the hole.
newtype Mortise a = Mortise { unMortise :: a }
  deriving newtype Show

-- | A newtype to add a type level witness that differentiates between a @Tenon@
-- tongue which fills a @Mortise@ hole.
newtype Tenon a = Tenon { unTenon :: a }
  deriving newtype Show

-- | helper function to construct a @Mortise@
mortise :: a -> Mortise a
mortise = Mortise

-- | helper function to construct a @Tenon@
tenon :: a -> Tenon a
tenon = Tenon

notRightLength :: Natural -> Syntax -> ExpansionErr
notRightLength n = NotRightLength [n]

data TypeCheckError
  = TypeMismatch (Maybe SrcLoc) Ty Ty (Maybe (Ty, Ty))
    -- ^ Blame for constraint, expected, got, and specific part that doesn't match
  | OccursCheckFailed MetaPtr Ty
  deriving (Show)

data KindCheckError
  = KindMismatch (Maybe SrcLoc) Kind Kind
  | KindOccursCheckFailed KindVar Kind
  deriving (Show)

data SyntacticCategory
  = ModuleCat
  | DeclarationCat
  | TypeCat
  | ExpressionCat
  | PatternCaseCat
  | TypePatternCaseCat
  deriving Show

instance Pretty VarInfo ExpansionErr where
  pp env (Ambiguous p x candidates) =
    hang 4 $
      text "Ambiguous identifier in phase" <+> pp env p <+> line <>
      text "Identifier:" <+> pp env x <> line <>
      text "Scope set of the identifier:" <> line <>
        viaShow (_stxScopeSet x) <> line <>
      text "Scope sets of the candidates:" <> line <>
        vsep [viaShow c | c <- toList candidates]
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
  pp env (NotConsCons stx) =
    hang 2 $ group $ vsep [text "Expected parens with at least 2 entries, but got", pp env stx]
  pp env (NotList stx) =
    hang 2 $ group $ vsep [text "Expected parens, but got", pp env stx]
  pp env (NotInteger stx) =
    hang 2 $ group $
    vsep [ text "Expected integer literal, but got"
         , pp env stx
         ]
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
  pp env (NotRightLength lengths0 stx) =
    hang 2 $ group $
    vsep [ text "Expected" <+> alts lengths0 <+> text "entries between parentheses, but got"
         , pp env stx
         ]
    where
      alts :: [Natural] -> Doc ann
      alts []
        = error "internal error: NotRightLength doesn't offer any acceptable lengths"
      alts [len]
        = viaShow len
      alts [len1, len2]
        = viaShow len1 <+> "or" <+> viaShow len2
      alts (len:lengths)
        = viaShow len <> "," <+> alts lengths
  pp env (NotVec stx) =
    hang 2 $ group $ vsep [text "Expected square-bracketed vec but got", pp env stx]
  pp env (NotImportSpec stx) =
    hang 2 $ group $ vsep [text "Expected import spec but got", pp env stx]
  pp env (NotExportSpec stx) =
    hang 2 $ group $ vsep [text "Expected export spec but got", pp env stx]
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
    hang 4 $ group $
    vsep [text "Error at phase" <+> pp env p <> text ":",
          pp env err]
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
  pp env (ImportError err) = pp env err
  pp _env (InternalError str) =
    text "Internal error during expansion! This is a bug in the implementation." <> line <> string str
  pp _env (ReaderError txt) =
    vsep (map text (T.lines txt))
  pp env (WrongSyntacticCategory stx is shouldBe) =
    hang 2 $ group $
    vsep [ pp env stx <> text ":"
         , group $ vsep [ group $ hang 2 $
                          vsep [ text "Used in a position expecting"
                               , pp env (unMortise shouldBe)
                               ]
                        , group $ hang 2 $
                          vsep [ text "but is valid in a position expecting"
                               , pp env (unTenon is)
                               ]
                        ]
         ]
  pp env (NotValidType stx) =
    hang 2 $ group $ vsep [text "Not a type:", pp env stx]
  pp env (TypeCheckError err) = pp env err
  pp env (KindCheckError err) = pp env err
  pp env (WrongArgCount stx ctor wanted got) =
    hang 2 $
    vsep [ text "Wrong number of arguments for constructor" <+> pp env ctor
         , text "Wanted" <+> viaShow wanted
         , text "Got" <+> viaShow got
         , text "At" <+> align (pp env stx)
         ]
  pp env (NotAConstructor stx) =
    hang 2 $ group $ vsep [text "Not a constructor in", pp env stx]
  pp env (WrongTypeArity stx ctor arity got) =
    hang 2 $ vsep [ text "Incorrect arity for" <+> pp env ctor
                  , text "Wanted" <+> viaShow arity
                  , text "Got" <+> viaShow got
                  , text "In" <+> align (pp env stx)
                  ]
  pp env (CircularImports current stack) =
    hang 2 $ vsep [ group $ vsep [ text "Circular imports while importing", pp env current]
                  , group $ hang 2 $ vsep (text "Context:" : map (pp env) stack)]

instance Pretty VarInfo TypeCheckError where
  pp env (TypeMismatch loc shouldBe got specifically) =
    group $ vsep [ group $ hang 2 $ vsep [ text "Type mismatch at"
                                         , maybe (text "unknown location") (pp env) loc <> text "."
                                         ]
                 , group $ vsep $
                   [ group $ hang 2 $ vsep [ text "Expected"
                                           , pp env shouldBe
                                           ]
                   , group $ hang 2 $ vsep [ text "but got"
                                           , pp env got
                                           ]
                   ] ++
                   case specifically of
                     Nothing -> []
                     Just (expected', got') ->
                       [ hang 2 $ group $ vsep [text "Specifically,"
                                               , group (vsep [ pp env expected'
                                                             , text "doesn't match" <+> pp env got'
                                                             ])
                                               ]
                       ]
                 ]

  pp env (OccursCheckFailed ptr ty) =
    hang 2 $ group $ vsep [ text "Infinite type detected:"
                          , group (vsep [viaShow ptr, "=", pp env ty])
                          ]

instance Pretty VarInfo KindCheckError where
  pp env (KindMismatch loc k1 k2) =
    hang 2 $ group $ vsep [ text "Kind mismatch at" <+>
                            maybe (text "unknown location") (pp env) loc <> text "."
                          , group $ vsep [pp env k1, text "≠", pp env k2]
                          ]

  pp env (KindOccursCheckFailed v k) =
    hang 2 $ group $ vsep [ text "Infinite kind detected:"
                          , group (vsep [viaShow v, "=", pp env k])
                          ]

instance Pretty VarInfo SyntacticCategory where
  pp _env ExpressionCat = text "an expression"
  pp _env ModuleCat = text "a module"
  pp _env TypeCat = text "a type"
  pp _env DeclarationCat = text "a top-level declaration or example"
  pp _env PatternCaseCat = text "a pattern"
  pp _env TypePatternCaseCat = text "a typecase pattern"
