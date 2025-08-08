{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings     #-}
module Expander.Error
  ( ExpansionErr, expansionError, ErrorKind(..), unExpansionErr
  , SyntacticCategory(..)
  , TypeCheckError(..)
  , Tenon, tenon, Mortise, mortise
  ) where

import Control.Lens
import Numeric.Natural
import Data.Text (Text)
import Data.Sequence (Seq)
import qualified Data.Text as T
import Data.Foldable
import Data.Traversable (for)

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

newtype ExpansionErr = ExpansionErr { unExpansionErr :: (Phase, ErrorKind) }
                       deriving Show

expansionError :: Phase -> ErrorKind -> ExpansionErr
expansionError p e = ExpansionErr (p,e)

data ErrorKind
  = Ambiguous Ident (Seq ScopeSet)
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
  | MacroEvaluationError EState
  | ValueNotMacro EState
  | ValueNotSyntax Value
  | ImportError KlisterPathError
  | InternalError String
  | NoSuchFile String
  | NotExported Ident
  | ReaderError Text
  | WrongSyntacticCategory Syntax
      (Tenon SyntacticCategory)
      (Mortise SyntacticCategory)
  | NotValidType Syntax
  | TypeCheckError TypeCheckError
  | WrongArgCount Syntax Constructor Int Int
  | NotAConstructor Syntax
  | WrongTypeArity Syntax TypeConstructor Natural Int
  | KindMismatch (Maybe SrcLoc) Kind Kind
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

data TypeCheckError
  = TypeMismatch (Maybe SrcLoc) Ty Ty (Maybe (Ty, Ty))
    -- ^ Blame for constraint, expected, got, and specific part that doesn't match
  | OccursCheckFailed MetaPtr Ty
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
  pp env (unExpansionErr -> (ppM, Ambiguous x candidates)) = do
    ppX <- pp env x
    ppP <- pp env ppM
    pure $ hang 4 $
      text "Ambiguous identifier in Phase" <+> ppP <+> line <>
      text "Identifier:" <+> ppX <> line <>
      text "Scope set of the identifier:" <> line <>
        viaShow (_stxScopeSet x) <> line <>
      text "Scope sets of the candidates:" <> line <>
        vsep [viaShow c | c <- toList candidates]
  pp env (unExpansionErr -> (ppM, Unknown x)) = do
    ppX <- pp env x
    ppP <- pp env ppM
    pure $
      text "In Phase:" <+> ppP
      <> line <> text "Unknown:" <+> ppX
  pp env (unExpansionErr -> (ppM, NoProgress tasks)) = do
    ppTasks <- mapM (pp env) tasks
    ppP <- pp env ppM
    pure $ hang 4 $
      text "In Phase:" <+> ppP <> line <>
      text "No progress was possible:" <> line <>
      vsep ppTasks
  pp env (unExpansionErr -> (ppM, NotIdentifier stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $
      vsep [ text "In Phase:" <+> ppP
           , indent 2 $ text "Not an identifier:" <+> ppStx
           ]
  pp env (unExpansionErr -> (ppM, NotEmpty stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group $ vsep [ text "In Phase:" <+> ppP
                                 , text "Expected (), but got", ppStx
                                 ]
  pp env (unExpansionErr -> (ppM, NotCons stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group $ vsep [ text "In Phase:" <+> ppP
                                 , text "Expected non-empty parens, but got", ppStx
                                 ]
  pp env (unExpansionErr -> (ppM, NotConsCons stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group $ vsep [ text "In Phase:" <+> ppP
                                 , text "Expected parens with at least 2 entries, but got", ppStx
                                 ]
  pp env (unExpansionErr -> (ppM, NotList stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group $ vsep [ text "In Phase:" <+> ppP
                                 , text "Expected parens, but got", ppStx
                                 ]
  pp env (unExpansionErr -> (ppM, NotInteger stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group
         $ vsep [ text "In Phase:" <+> ppP
                , text "Expected integer literal, but got"
                , ppStx
                ]
  pp env (unExpansionErr -> (ppM, NotString stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group
         $ vsep [ text "In Phase:" <+> ppP
                , text "Expected string literal, but got"
                , ppStx
                ]
  pp env (unExpansionErr -> (ppM, NotModName stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group
         $ vsep [ text "In Phase:" <+> ppP
                , text "Expected module name (string or `kernel'), but got"
                , ppStx
                ]
  pp env (unExpansionErr -> (ppM, NotRightLength lengths0 stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group
         $ vsep [ text "In Phase:" <+> ppP
                , text "Expected" <+> alts lengths0 <+> text "entries between parentheses, but got"
                , ppStx
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
  pp env (unExpansionErr -> (ppM, NotVec stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group $ vsep [ text "In Phase:" <+> ppP
                                 , text "Expected square-bracketed vec but got", ppStx
                                 ]
  pp env (unExpansionErr -> (ppM, NotImportSpec stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group $ vsep [text "In Phase:" <+> ppP, text "Expected import spec but got", ppStx]
  pp env (unExpansionErr -> (ppM, NotExportSpec stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group $ vsep [text "In Phase:" <+> ppP, text "Expected export spec but got", ppStx]
  pp env (unExpansionErr -> (ppM, UnknownPattern stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group $ vsep [ text "In Phase" <+> ppP
                                 , text "Unknown pattern"
                                 , ppStx
                                 ]
  pp env (unExpansionErr -> (ppM, MacroRaisedSyntaxError err)) = do
    let locs = view syntaxErrorLocations err
    ppErr <- pp env (view syntaxErrorMessage err)
    ppP   <- pp env ppM
    let ppMsg = text "In Phase:" <+> ppP <> line
                <> text "Syntax error from macro:" <> line <> ppErr
    ppBlock <- case locs of
      [] -> pure ppMsg
      (Syntax l : ls) -> do
        ppSrcLoc <- pp env (view stxSrcLoc l)
        ppLs <- case ls of
          [] -> pure mempty
          more -> do
            ppMore <- for more $ \(Syntax (Stx _ loc _)) ->
              pp env loc
            pure $ text "Additional locations:" <> line <> vsep ppMore
        pure (ppSrcLoc <> text ":" <> line <> ppMsg <> ppLs)
    pure $ hang 4 $ group ppBlock
  pp env (unExpansionErr -> (ppM, MacroEvaluationError err)) = do
    ppErr <- pp env err
    ppP   <- pp env ppM
    pure $ hang 4 $ group
         $ vsep [text "In Phase:" <+> ppP <> text ":",
                 ppErr]
  pp env (unExpansionErr -> (ppM, ValueNotMacro val)) = do
    ppVal <- pp env val
    ppP   <- pp env ppM
    pure $ vsep [ text "In Phase:" <+> ppP
                , text "Not a macro monad value:" <+> ppVal
                ]
  pp env (unExpansionErr -> (ppM, ValueNotSyntax val)) = do
    ppVal <- pp env val
    ppP   <- pp env ppM
    pure $ hang 4
      $ group
      $ text "In Phase:" <+> ppP <> line
      <> text "Not a syntax object: "
      <> line <> ppVal

  pp _env (unExpansionErr -> (_, NoSuchFile filename)) =
    pure $ text "User error; no such file: " <> string filename
  pp env (unExpansionErr -> (ppM, NotExported (Stx _ loc x))) = do
    ppLoc <- pp env loc
    ppP   <- pp env ppM
    ppX <- pp env x
    pure $ group $ hang 4 $ vsep [ ppLoc <> text ":"
                          , text "Not available at phase" <+> ppP <> text ":" <+> ppX
                          ]
  pp env (unExpansionErr -> (_,ImportError err)) = pp env err
  pp env (unExpansionErr -> (ppM, InternalError str)) = do
    ppP <- pp env ppM
    return
      $ text "In Phase:" <+> ppP <> line
      <> text "Internal error during expansion! This is a bug in the implementation."
      <> line <> string str
  pp _env (unExpansionErr -> (_, ReaderError txt)) =
    pure $ vsep (map text (T.lines txt))
  pp env (unExpansionErr -> (ppM, WrongSyntacticCategory stx is shouldBe)) = do
    ppStx <- pp env stx
    ppIs  <- pp env (unTenon is)
    ppP   <- pp env ppM
    ppShouldBe <- pp env (unMortise shouldBe)
    pure $
      vsep [ text "In Phase:" <+> ppP
           , indent 2 (ppStx <> text ":")
           , indent 2
             $ vsep [ text "Used in a position expecting:"
                    , indent 2 ppShouldBe
                    , text "but is valid in a position expecting:"
                    , indent 2 ppIs
              ]
           ]
  pp env (unExpansionErr -> (ppM, NotValidType stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group $ vsep [ text "In Phase:" <+> ppP
                                 , text "Not a type:", ppStx
                                 ]
  pp env (unExpansionErr -> (_ppM, TypeCheckError err)) = pp env err
  pp env (unExpansionErr -> (ppM, WrongArgCount stx ctor wanted got)) = do
    ppCtor <- pp env ctor
    ppStx  <- pp env stx
    ppP    <- pp env ppM
    pure $ hang 2
         $ vsep [ text "In Phase:" <+> ppP
                , text "Wrong number of arguments for constructor" <+> ppCtor
                , text "Wanted" <+> viaShow wanted
                , text "Got" <+> viaShow got
                , text "At" <+> align (ppStx)
                ]
  pp env (unExpansionErr -> (ppM, NotAConstructor stx)) = do
    ppStx <- pp env stx
    ppP   <- pp env ppM
    pure $ hang 2 $ group $ vsep [ text "In Phase:" <+> ppP
                                 , text "Not a constructor in"
                                 , ppStx
                                 ]
  pp env (unExpansionErr -> (ppM, WrongTypeArity stx ctor arity got)) = do
    ppCtor <- pp env ctor
    ppStx  <- pp env stx
    ppP    <- pp env ppM
    pure $ hang 2 $ vsep [ text "In Phase" <+> ppP
                         , text "Incorrect arity for" <+> ppCtor
                         , text "Wanted" <+> viaShow arity
                         , text "Got" <+> viaShow got
                         , text "In" <+> align (ppStx)
                         ]
  pp env (unExpansionErr -> (ppM, KindMismatch loc k1 k2)) = do
    ppLoc <- maybe (pure $ text "unknown location") (pp env) loc
    ppK1 <- pp env k1
    ppK2 <- pp env k2
    ppP  <- pp env ppM
    pure
      $ hang 2
      $ group
      $ vsep [ text "In Phase:" <+> ppP
             , text "Kind mismatch at" <+> ppLoc <> text "."
             , group $ vsep [ppK1, text "≠", ppK2]
             ]
  pp env (unExpansionErr -> (_ppM, CircularImports current stack)) = do
    ppCurrent <- pp env current
    ppStack <- mapM (pp env) stack
    pure $ hang 2 $ vsep [ group $ vsep [ text "Circular imports while importing", ppCurrent]
                  , group $ hang 2 $ vsep (text "Context:" : ppStack)]

instance Pretty VarInfo TypeCheckError where
  pp env (TypeMismatch loc shouldBe got specifically) = do
    ppLoc <- maybe (pure $ text "unknown location") (pp env) loc
    ppShouldBe <- pp env shouldBe
    ppGot <- pp env got
    ppSpec <- case specifically of
      Nothing -> pure []
      Just (expected', got') -> do
        ppE <- pp env expected'
        ppG <- pp env got'
        pure [ hang 2 $ group $ vsep [text "Specifically,"
                                    , group (vsep [ ppE
                                                , text "doesn't match" <+> ppG
                                                ])
                                    ]
            ]
    pure $ group $ vsep [ group $ hang 2 $ vsep [ text "Type mismatch at"
                                                , ppLoc <> text "."
                                                ]
                       , group $ vsep $
                         [ group $ hang 2 $ vsep [ text "Expected"
                                                , ppShouldBe
                                                ]
                         , group $ hang 2 $ vsep [ text "but got"
                                                , ppGot
                                                ]
                         ] ++ ppSpec
                       ]

  pp env (OccursCheckFailed ptr ty) = do
    ppTy <- pp env ty
    pure $ hang 2 $ group $ vsep [ text "Occurs check failed:"
                          , group (vsep [viaShow ptr, "≠", ppTy])
                          ]


instance Pretty VarInfo SyntacticCategory where
  pp _env ExpressionCat      = pure $ text "an expression"
  pp _env ModuleCat          = pure $ text "a module"
  pp _env TypeCat            = pure $ text "a type"
  pp _env DeclarationCat     = pure $ text "a top-level declaration or example"
  pp _env PatternCaseCat     = pure $ text "a pattern"
  pp _env TypePatternCaseCat = pure $ text "a typecase pattern"
