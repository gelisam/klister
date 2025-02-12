{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Pretty (Doc, Pretty(..), string, text, viaShow, (<+>), (<>), align, hang, line, group, vsep, hsep, VarInfo(..), pretty, prettyPrint, prettyPrintLn, prettyEnv, prettyPrintEnv) where

import Control.Lens hiding (List)
import Control.Monad.State
import qualified Data.HashMap.Strict as HM
import Util.Set (Set)
import qualified Util.Set as Set
import Prettyprinter hiding (Pretty(..), angles, parens)
import qualified Prettyprinter as PP
import Prettyprinter.Render.Text (putDoc, renderStrict)
import Data.Sequence (Seq)
import Data.Text (Text)
import Data.Traversable (for)
import qualified Data.Text as T
import qualified Data.Foldable as F
import System.FilePath (takeFileName)

import Binding
import Binding.Info
import Core
import Datatype
import Env
import Evaluator (EvalResult(..), EvalError(..), TypeError(..))
import Kind
import Module
import ModuleName
import KlisterPath
import Phase
import Scope
import ScopeSet
import Syntax
import Syntax.SrcLoc
import Type
import Unique
import Value
import World

import Util.Store (Store)
import qualified Util.Store as St

text :: Text -> Doc ann
text = PP.pretty

string :: String -> Doc ann
string = PP.pretty

parens :: Doc ann -> Doc ann
parens doc = text "(" <> align (group doc) <> ")"

angles :: Doc ann -> Doc ann
angles doc = text "⟨" <> align (group doc) <> "⟩"

vec :: Doc ann -> Doc ann
vec doc = text "[" <> align (group doc) <> "]"

pretty :: Pretty ann a => a -> Text
pretty x
  = renderStrict
  $ layoutPretty defaultLayoutOptions
  $ flip evalState St.empty
  $ pp Env.empty x

prettyPrint :: Pretty ann a => a -> IO ()
prettyPrint x
  = putDoc
  $ flip evalState St.empty
  $ pp Env.empty x

prettyPrintLn :: Pretty ann a => a -> IO ()
prettyPrintLn x = do
  prettyPrint x
  putStrLn ""

prettyEnv :: Pretty ann a => Env Var v -> a -> Text
prettyEnv env x
  = renderStrict
  $ layoutPretty defaultLayoutOptions
  $ flip evalState St.empty
  $ pp (fmap (const ()) env) x

prettyPrintEnv :: Pretty ann a => Env Var v -> a -> IO ()
prettyPrintEnv env x
  = putDoc
  $ flip evalState St.empty
  $ pp (fmap (const ()) env) x


-- Internally, the type of 'id' might be represented as @MetaPtr 183 -> MetaPtr
-- 186@, with some information about the unification variables indicating that
-- 183 and 186 are the same. When we print this, we would prefer to show
-- something like @?1 -> ?1@. To achieve this, the caller (who has access to the
-- information about the unification variables) must zonk the type into @MetaPtr
-- 183 -> MetaPtr 183@, and the pretty-printer must keep track of which
-- unification variables it has already printed and which number it used for
-- each.
type Renumbering = Store MetaPtr Int

class Pretty ann a | a -> ann where
  pp :: Env Var () -> a -> State Renumbering (Doc ann)

instance Pretty ann (Doc ann) where
  pp _env doc = pure doc

data VarInfo
  = BindingSite Var
  | MacroBindingSite MacroVar
  | UseSite Var

instance Pretty VarInfo Core where
  pp env (Core e) = pp env e

instance (PrettyBinder VarInfo typePat, PrettyBinder VarInfo pat, Pretty VarInfo core) =>
         Pretty VarInfo (CoreF typePat pat core) where
  pp env (CoreVar v) =
    pure $ annotate (UseSite v) $
    case Env.lookupIdent v env of
      Nothing -> string ("!!" ++ show v ++ "!!")
      Just (Stx _ _ x) -> text x
  pp env (CoreLet x@(Stx _ _ y) v def body) = do
    ppY <- pp env y
    ppDef <- pp env def
    ppBody <- pp (env <> Env.singleton v x ()) body
    pure $ hang 2 $ group $
      vsep [ text "let" <+> hang 2 (group (vsep [ ppY <+> text "="
                                               , ppDef
                                               ])) <+> text "in"
           , ppBody
           ]
  pp env (CoreLetFun f@(Stx _ _ g) fv x@(Stx _ _ y) v def body) = do
    ppG <- pp env g
    ppY <- pp env y
    ppDef <- pp (env <> Env.singleton fv f () <> Env.singleton v x ()) def
    ppBody <- pp (env <> Env.singleton fv f ()) body
    pure $ hang 2 $ group $
      vsep [ text "flet" <+>
             hang 2 (group (vsep [ ppG <+> ppY <+> text "="
                                 , ppDef
                                 ])) <+>
             text "in"
           , ppBody
           ]
  pp env (CoreLam n@(Stx _ _ x) v body) = do
    ppBody <- pp (env <> Env.singleton v n ()) body
    pure $ hang 2 $ group $
      text "λ" <> annotate (BindingSite v) (text x) <> "." <> line <>
      ppBody
  pp env (CoreApp fun arg) = do
    ppFun <- pp env fun
    ppArg <- pp env arg
    pure $ parens (ppFun <> line <> ppArg)
  pp env (CoreCtor ctor []) = pp env ctor
  pp env (CoreCtor ctor args) = do
    ppCtor <- pp env ctor
    ppArgs <- mapM (pp env) args
    pure $ hang 2 $ parens $ ppCtor <+> group (vsep ppArgs)
  pp env (CoreDataCase _ scrut cases) = do
    ppScrut <- pp env scrut
    ppCases <- for cases $ \(pat, rhs) -> do
      (ppPat, env') <- ppBind env pat
      ppRhs <- pp (env <> env') rhs
      pure $ hang 2 $ group $ vsep [ppPat <+> text "↦", ppRhs]
    pure $ hang 2 $ group $
      vsep [ text "case" <+> ppScrut <+> "of"
           , encloseSep (flatAlt mempty (text "{" <> space))
                        (flatAlt mempty (space <> text "}"))
                        (flatAlt mempty (space <> text ";" <> space)) ppCases
           ]
  pp _env (CoreString str) = pure $ text (T.pack (show str))
  pp env (CoreError what) = do
    ppWhat <- pp env what
    pure $ text "error" <+> ppWhat
  pp env (CorePureMacro arg) = do
    ppArg <- pp env arg
    pure $ text "pure" <+> ppArg
  pp env (CoreBindMacro act k) = do
    ppAct <- pp env act
    ppK <- pp env k
    pure $ hang 2 $ group (ppAct <+> text ">>=") <+> ppK
  pp env (CoreSyntaxError err) = do
    ppErr <- pp env err
    pure $ group $ text "syntax-error" <+> ppErr
  pp env (CoreIdentEq how e1 e2) = do
    ppE1 <- pp env e1
    ppE2 <- pp env e2
    pure $ group $ text opName <+> ppE1 <+> ppE2
    where
      opName =
        case how of
          Free -> "free-identifier=?"
          Bound -> "bound-identifier=?"
  pp env (CoreLog msg) = do
    ppMsg <- pp env msg
    pure $ group (hang 2 (vsep ["log", ppMsg]))
  pp _env CoreMakeIntroducer = pure $ text "make-introducer"
  pp _ CoreWhichProblem = pure $ text "which-problem"
  pp env (CoreSyntax stx) = pp env stx
  pp env (CoreCase _ scrut pats) = do
    ppScrut <- pp env scrut
    ppPats <- for pats $ \(pat, body) -> do
      (b, env') <- ppBind env pat
      ppBody <- pp (env <> env') body
      pure $ parens $ hang 2 $ group (group (b <+> "=>") <> line <> ppBody)
    pure $ hang 2 $ group $
      group (hang 2 $ text "syntax-case" <+> ppScrut <+> "of") <> line <>
      vsep ppPats
  pp _env (CoreInteger s) = pure $ viaShow s
  pp env (CoreIdent x) = pp env x
  pp env (CoreEmpty e) = pp env e
  pp env (CoreCons e) = pp env e
  pp env (CoreList e) = pp env e
  pp env (CoreIntegerSyntax i) = pp env i
  pp env (CoreStringSyntax s) = pp env s
  pp env (CoreReplaceLoc loc stx) = do
    ppLoc <- pp env loc
    ppStx <- pp env stx
    pure $ group $ hang 2 $ vsep [ text "replace-loc"
                                 , ppLoc
                                 , ppStx
                                 ]
  pp env (CoreTypeCase _ scrut pats) = do
    ppScrut <- pp env scrut
    ppPats <- for pats $ \(pat, body) -> do
      (b, env') <- ppBind env pat
      ppBody <- pp (env <> env') body
      pure $ parens $ hang 2 $ group (group (b <+> "=>") <> line <> ppBody)
    pure $ hang 2 $ group $
      group (hang 2 $ text "type-case" <+> ppScrut <+> "of") <> line <>
      vsep ppPats

instance Pretty VarInfo core => Pretty VarInfo (SyntaxError core) where
  pp env err = do
    ppMsg <- pp env (view syntaxErrorMessage err)
    ppLocs <- mapM (pp env) (view syntaxErrorLocations err)
    pure $ angles $ ppMsg <> text ";" <+> concatWith (\d1 d2 -> d1 <> text "," <+> d2) ppLocs

class PrettyBinder ann a | a -> ann where
  ppBind :: Env Var () -> a -> State Renumbering (Doc ann, Env Var ())


instance PrettyBinder VarInfo a => PrettyBinder VarInfo (TyF a) where
  ppBind env t = do
    let subs = ppBind env <$> t
    sub <- sequence subs
    doc <- pp env (fmap fst sub)
    pure (doc, foldMap snd sub)

newtype BinderPair = BinderPair (Ident, Var)

instance PrettyBinder VarInfo BinderPair where
  ppBind _env (BinderPair (ident@(Stx _ _ n), x)) =
    pure (annotate (BindingSite x) (text n), Env.singleton x ident ())

instance PrettyBinder VarInfo TypePattern where
  ppBind env (TypePattern t) =
    ppBind env (fmap BinderPair t)
  ppBind env (AnyType ident x) =
    ppBind env (BinderPair (ident, x))

instance PrettyBinder VarInfo ConstructorPattern where
  ppBind env pat = ppBind env (unConstructorPattern pat)

instance PrettyBinder VarInfo a => PrettyBinder VarInfo (ConstructorPatternF a) where
  ppBind env (CtorPattern ctor subPats) =
    case subPats of
      [] -> do
        doc <- pp env ctor
        pure (doc, Env.empty)
      _nonEmpty -> do
        subDocs <- mapM (ppBind env) subPats
        doc <- pp env ctor
        pure (doc <+> hsep (map fst subDocs),
              foldr (<>) Env.empty (map snd subDocs))
  ppBind _env (PatternVar ident@(Stx _ _ n) x) =
    pure (annotate (BindingSite x) (text n), Env.singleton x ident ())

instance PrettyBinder VarInfo SyntaxPattern where
  ppBind _env (SyntaxPatternIdentifier ident@(Stx _ _ x) v) =
    pure (annotate (BindingSite v) (text x), Env.singleton v ident ())
  ppBind _env (SyntaxPatternInteger ident@(Stx _ _ x) v) =
    pure (parens $ text "integer" <+> annotate (BindingSite v) (text x), Env.singleton v ident ())
  ppBind _env (SyntaxPatternString ident@(Stx _ _ x) v) =
    pure (parens $ text "string" <+> annotate (BindingSite v) (text x), Env.singleton v ident ())
  ppBind _env SyntaxPatternEmpty =
    pure (text "()", Env.empty)
  ppBind _env (SyntaxPatternCons ida@(Stx _ _ xa) va idd@(Stx _ _ xd) vd) =
    pure (parens (text "cons" <+>
             annotate (BindingSite va) (text xa) <+>
             annotate (BindingSite vd) (text xd)),
     Env.insert vd idd () $ Env.singleton va ida ())
  ppBind _env (SyntaxPatternList vars) =
    pure (vec $
     hsep [annotate (BindingSite v) (text x)
          | (Stx _ _ x, v) <- vars
          ],
     foldr (\(x, v) e -> Env.insert x v () e) Env.empty [(v, x) | (x, v) <- vars])
  ppBind _env SyntaxPatternAny = pure (text "_", Env.empty)

instance Pretty VarInfo core => Pretty VarInfo (ScopedIdent core) where
  pp env ident = do
    ppIdent <- pp env (view scopedIdentIdentifier ident)
    ppScope <- pp env (view scopedIdentScope ident)
    pure $ text "ident" <+> ppIdent <+> ppScope

instance Pretty VarInfo core => Pretty VarInfo (ScopedEmpty core) where
  pp env e = do
    ppScope <- pp env (view scopedEmptyScope e)
    pure $ text "()" <> angles ppScope

instance Pretty VarInfo core => Pretty VarInfo (ScopedCons core) where
  pp env pair = do
    ppHead <- pp env (view scopedConsHead pair)
    ppTail <- pp env (view scopedConsTail pair)
    ppScope <- pp env (view scopedConsScope pair)
    pure $ text "cons-from" <>
      parens (ppHead <> text "," <+> ppTail) <>
      angles ppScope

instance Pretty VarInfo core => Pretty VarInfo (ScopedList core) where
  pp env xs = do
    ppElements <- mapM (pp env) (view scopedListElements xs)
    ppScope <- pp env (view scopedListScope xs)
    pure $ vec (hsep ppElements) <> angles ppScope

instance Pretty VarInfo core => Pretty VarInfo (ScopedInteger core) where
  pp env s = do
    ppInteger <- pp env (view scopedInteger s)
    ppScope <- pp env (view scopedIntegerScope s)
    pure $ ppInteger <> angles ppScope

instance Pretty VarInfo core => Pretty VarInfo (ScopedString core) where
  pp env s = do
    ppString <- pp env (view scopedString s)
    ppScope <- pp env (view scopedStringScope s)
    pure $ ppString <> angles ppScope

instance PrettyBinder VarInfo CompleteDecl where
  ppBind env (CompleteDecl d) = ppBind env d

instance PrettyBinder VarInfo (Seq CompleteDecl) where
  ppBind env decls = do
    (docs, env') <- F.foldrM go ([], mempty) decls
    pure (vsep docs, env')
    where
      go :: CompleteDecl
         -> ([Doc VarInfo], Env Var ())
         -> State Renumbering ([Doc VarInfo], Env Var ())
      go decl (docs, e) = do
        (doc, e') <- ppBind (env <> e) decl
        pure (doc:docs, e <> e')

instance Pretty VarInfo Kind where
  pp _   KStar        = pure $ text "*"
  pp env (KFun k1 k2) = do
    ppK1 <- pp env k1
    ppK2 <- pp env k2
    pure $ parens (ppK1 <+> text "→" <+> ppK2)
  pp _   (KMetaVar v) = pure $ text "META" <> viaShow v -- TODO make it look better

instance Pretty VarInfo (Scheme Ty) where
  pp env (Scheme [] t) = pp env t
  pp env (Scheme argKinds t) = do
    ppT <- pp env t
    ppArgKinds <- mapM (pp env) argKinds
    pure $ text "∀" <>
      (align $ group $
       vsep [ group $
              vsep (zipWith ppArgKind typeVarNames ppArgKinds) <> text "."
            , ppT
            ])
    where
      ppArgKind varName kind = parens (text varName <+> text ":" <+> kind)

typeVarNames :: [Text]
typeVarNames =
  greek ++
  [ base <> T.pack (show i)
  | (base, i) <- greekNum
  ]
  where
    greek = [ T.pack [letter]
            | letter <- "αβγδεζηθικλμνξοπρστυφχψω"
            ]
    greekNum = [ (base, num)
               | num <- [(0 :: Integer)..]
               , base <- greek
               ]

instance Pretty VarInfo TypeConstructor where
  pp _   TSyntax        = pure $ text "Syntax"
  pp _   TInteger       = pure $ text "Integer"
  pp _   TString        = pure $ text "String"
  pp _   TOutputPort    = pure $ text "Output-Port"
  pp _   TFun           = pure $ text "(→)"
  pp _   TMacro         = pure $ text "Macro"
  pp _   TIO            = pure $ text "IO"
  pp _   TType          = pure $ text "Type"
  pp env (TDatatype t)  = pp env t
  pp _   (TSchemaVar n) = pure $ text $ typeVarNames !! fromIntegral n
  pp _   (TMetaVar v)   = do
    renumbering <- get
    case St.lookup v renumbering of
      Just n -> do
        pure $ text "?" <> viaShow n
      Nothing -> do
        let n = St.size renumbering + 1
        put (St.insert v n renumbering)
        pure $ text "?" <> viaShow n

instance Pretty VarInfo a => Pretty VarInfo (TyF a) where
  pp _ (TyF TFun []) = pure $ parens (text "→")
  pp env (TyF TFun [a]) = do
    ppA <- pp env a
    pure $ parens (text "→" <+> ppA)
  pp env (TyF TFun [a, b]) = do
    ppA <- pp env a
    ppB <- pp env b
    pure $ parens $ align $ group $ vsep [ppA <+> text "→", ppB]
  pp env (TyF ctor args) = do
    ppCtor <- pp env ctor
    case args of
      [] -> pure ppCtor
      more -> do
        ppMore <- mapM (pp env) more
        pure $ parens $ align $ group $ ppCtor <+> vsep ppMore

instance Pretty VarInfo Datatype where
  pp _ d = pure $ text (view (datatypeName . datatypeNameText) d)

instance Pretty VarInfo Constructor where
  pp _ c = pure $ text (view (constructorName . constructorNameText) c)

instance Pretty VarInfo Ty where
  pp env (Ty t) = pp env t

instance (Pretty VarInfo s, Pretty VarInfo t, PrettyBinder VarInfo a, Pretty VarInfo b) =>
         PrettyBinder VarInfo (Decl t s a b) where
  ppBind env (Define n@(Stx _ _ x) v t e) = do
    ppT <- pp env t
    ppE <- pp (env <> Env.singleton v n ()) e
    pure (hang 4 $ group $
          vsep [ text "define" <+>
                 annotate (BindingSite v) (text x) <+> text ":"
               , ppT
               , text ":="
               , ppE
               ],
          Env.singleton v n ())
  ppBind env (DefineMacros macros) = do
    ppMacros <- for macros $ \(Stx _ _ x, v, e) -> do
      ppE <- pp env e
      pure $ hang 2 $ group $
        annotate (MacroBindingSite v) (text x) <+> text "↦" <> line <> ppE
    pure (hang 4 $ text "define-macros" <> line <> vsep ppMacros, mempty)
  ppBind env (Data (Stx _ _ x) _dn argKinds ctors) = do
    ppArgKinds <- mapM (pp env) argKinds
    ppCtors <- for ctors $ \(Stx _ _ c, _cn, args) -> do
      ppArgs <- mapM (pp env) args
      pure $ case ppArgs of
        [] -> text c
        more -> hang 2 $ text c <+> group (vsep ppArgs)
    pure (hang 2 $ group $
            vsep ( text "data" <+> text x <+>
                   hsep [ parens (text α <+> ":" <+> kind)
                        | α <- typeVarNames
                        | kind <- ppArgKinds
                        ] <+>
                   text "="
                 : punc (space <> text "|") ppCtors
                 )
           , mempty)
  ppBind env (Meta d) = do
    (doc, env') <- ppBind env d
    pure (hang 4 $ text "meta" <> line <> doc, env')
  ppBind env (Import spec) = do
    ppSpec <- pp env spec
    pure (hang 4 $ text "import" <+> ppSpec, mempty)
  ppBind env (Export x) = do
    ppX <- pp env x
    pure (hang 4 $ text "export" <+> ppX, mempty)
  ppBind env (Example loc t e) = do
    ppLoc <- pp env loc
    ppT <- pp env t
    ppE <- pp env e
    pure (hang 4 $
            text "example@" <> ppLoc <+>
            align (group (vsep [ group (ppE) <+> text ":"
                               , ppT
                               ])),
            mempty)
  ppBind env (Run _loc e) = do
    ppE <- pp env e
    pure (hang 4 $
            text "run" <+> align ppE,
            mempty)

instance Pretty VarInfo ExportSpec where
  pp env (ExportIdents ids) = do
    ppIds <- mapM (pp env) ids
    pure $ text "{" <> align (vsep ppIds) <> text "}"
  pp env (ExportRenamed spec rens) = do
    ppSpec <- pp env spec
    let ppRens = map (\(x, y) -> text x <+> text "↦" <+> text y) rens
    pure $ align $ hang 2 $ group $
      ppSpec <> line <>
      text "renaming" <+> text "{" <>
      (align $ group $ vsep ppRens) <>
      text "}"
  pp env (ExportPrefixed spec p) = do
    ppSpec <- pp env spec
    pure $ align $ hang 2 $ group $
      vsep [ text "(" <> align (group ppSpec) <> ")"
           , text "with" <+> text "prefix"
           , text p
           ]
  pp env (ExportShifted spec i) = do
    ppSpec <- pp env spec
    pure $ align $ hang 2 $ group $
      vsep [ text "(" <> align (group ppSpec) <> ")"
           , text "shifted" <+> text "by"
           , viaShow i
           ]

instance Pretty VarInfo ImportSpec where
  pp env (ImportModule mn) = pp env mn
  pp env (ImportOnly spec ids) = do
    ppSpec <- pp env spec
    ppIds <- mapM (pp env) ids
    pure $ group $ vsep [ text "only"
                          , ppSpec
                          , parens (group (vsep ppIds))
                          ]
  pp env (ShiftImports spec i) = do
    ppSpec <- pp env spec
    pure $ ppSpec <+> "⇑" <+> viaShow i
  pp env (RenameImports spec rens) = do
    ppSpec <- pp env spec
    ppRens <- mapM (\(x, y) -> (<+>) <$> pp env x <*> pp env y) rens
    pure $ group $ vsep [ text "rename"
                        , ppSpec
                        , group (vsep ppRens)
                        ]
  pp env (PrefixImports spec pref) = do
    ppSpec <- pp env spec
    pure $ group $ vsep [ text "prefix"
                        , ppSpec
                        , viaShow pref
                        ]

instance Pretty VarInfo ModuleName where
  pp _ n = pure $ text (moduleNameText n)

instance (Functor f, Traversable f, PrettyBinder VarInfo a) => Pretty VarInfo (Module f a) where
  pp env m = do
    let modName = view moduleName m
    let body = view moduleBody m
    ppModName <- pp env modName
    ppBody <- flip evalStateT env $ traverse go body
    pure $ hang 4 $
      text "module" <+> ppModName <> line <>
      concatWith terpri ppBody
    where
      terpri d1 d2 = d1 <> line <> d2
      go :: a -> StateT (Env Var ()) (State Renumbering) (Doc VarInfo)
      go d = do
        thisEnv <- get
        (doc, newEnv) <- lift $ ppBind thisEnv d
        put (thisEnv <> newEnv)
        pure doc

instance Pretty VarInfo SrcLoc where
  pp env loc = do
    ppStart <- pp env (view srcLocStart loc)
    ppEnd <- pp env (view srcLocEnd loc)
    pure $ string (takeFileName (view srcLocFilePath loc)) <> text ":" <>
      ppStart <> text "-" <>
      ppEnd

instance Pretty VarInfo SrcPos where
  pp _env pos = pure $ viaShow (view srcPosLine pos) <> text "." <> viaShow (view srcPosCol pos)

instance Pretty VarInfo a => Pretty VarInfo (Stx a) where
  pp env (Stx _ loc v) = do
    ppLoc <- pp env loc
    ppV <- pp env v
    pure $ text "#" <>
      (align . group)
        (text "[" <> ppLoc <> text "]" <> line' <> text "<" <>
         align ppV <>
         text ">")

instance Pretty VarInfo Syntax where
  pp env (Syntax e) = pp env e

instance Pretty VarInfo (ExprF Syntax) where
  pp _   (Id x)      = pure $ text x
  pp _   (String s)  = pure $ viaShow s
  pp _   (Integer s) = pure $ viaShow s
  pp env (List xs)   = do
    ppXs <- mapM (pp env . syntaxE) xs
    pure $ parens (group (vsep ppXs))

instance Pretty VarInfo Closure where
  pp _ _ = pure $ text "#<closure>"

instance Pretty VarInfo Value where
  pp env (ValueClosure c) = pp env c
  pp env (ValueSyntax stx) = pp env stx
  pp env (ValueMacroAction act) = pp env act
  pp _env (ValueIOAction _) = pure "#<IO action>"
  pp _env (ValueOutputPort _) = pure "#<output port>"
  pp _env (ValueInteger s) = pure $ viaShow s
  pp _env (ValueCtor c []) = pure $ parens $ text (view (constructorName . constructorNameText) c)
  pp env (ValueCtor c args) = do
    ppArgs <- mapM (pp env) args
    pure $ parens $ text (view (constructorName . constructorNameText) c) <+> align (group (vsep ppArgs))
  pp _env (ValueType ptr) = pure $ text "#t<" <> viaShow ptr <> text ">"
  pp _env (ValueString str) = pure $ text (T.pack (show str))

instance Pretty VarInfo MacroAction where
  pp env (MacroActionPure v) = do
    ppV <- pp env v
    pure $ text "pure" <+> ppV
  pp env (MacroActionBind v k) = do
    ppV <- pp env v
    ppK <- pp env k
    pure $ group $
      group (ppV <> line <> text ">>=") <> line <>
      ppK
  pp env (MacroActionSyntaxError err) = do
    ppErr <- pp env err
    pure $ text "syntax-error" <+> ppErr
  pp env (MacroActionIdentEq how v1 v2) = do
    ppV1 <- pp env v1
    ppV2 <- pp env v2
    pure $ group $ parens $ vsep [text opName, ppV1, ppV2]
    where
      opName =
        case how of
          Free  -> "free-identifier=?"
          Bound -> "bound-identifier=?"
  pp env (MacroActionLog stx) = do
    ppStx <- pp env stx
    pure $ hang 2 $ group $ vsep [text "log", ppStx]
  pp _env MacroActionIntroducer = pure $ text "make-introducer"
  pp _env MacroActionWhichProblem = pure $ text "which-problem"
  pp env (MacroActionTypeCase venv _loc ptr cases) = do
    ppCases <- for cases $ \(pat, c) -> do
      (patDoc, env') <- ppBind env pat
      ppC <- pp (fmap (const ()) venv <> env') c
      pure $ hang 2 $ group $ vsep [patDoc <+> "↦", ppC]
    pure $ hang 2 $
      text "type-case" <+> text "#t<" <> viaShow ptr <> text ">" <+> text "of" <> line <>
      vsep ppCases

instance Pretty VarInfo Phase where
  pp _env p = pure $ text "p" <> viaShow (phaseNum p)

instance Pretty VarInfo a => Pretty VarInfo (World a) where
  pp env w = do
    ppModules <- for (HM.toList (view worldModules w)) $ \(_modName, mod) -> do
      pp env mod
    ppVisited <- for (HM.toList (view worldVisited w)) $ \(modName, phases) -> do
      ppModName <- pp env modName
      ppPhases <- mapM (pp env) (Set.toList phases)
      pure $ hang 4 $ ppModName <> line <> text "{" <> group (vsep ppPhases) <> text "}"
    ppEnvs <- for (St.toList $ view worldEnvironments w) $ \(p, rho) -> do
      ppPhase <- pp env p
      ppRho <- pp env rho
      pure $ hang 4 $ ppPhase <> line <> ppRho
    pure $ vsep $ map (hang 4)
      [vsep [ text "Expanded modules"
            , vsep ppModules
            ]
      , vsep [ text "Modules visited"
             , vsep ppVisited
             ]
      , vsep [ text "Environments"
             , hang 4 $ vsep ppEnvs
             ]
      ]

instance Pretty VarInfo Text where
  pp _ = pure . text

instance Pretty VarInfo a => Pretty VarInfo (Env Var a) where
  pp env rho = do
    ppRho <- for (Env.toList rho) $ \(x, n, v) -> do
      ppN <- pp env n
      ppV <- pp env v
      pure $ hang 4 $ viaShow x <+> ppN <> line <> ppV
    pure $ vsep ppRho

instance Pretty VarInfo a => Pretty VarInfo (Env MacroVar a) where
  pp env rho = do
    ppRho <- for (Env.toList rho) $ \(x, n, v) -> do
      ppN <- pp env n
      ppV <- pp env v
      pure $ hang 4 $ viaShow x <+> ppN <> line <> ppV
    pure $ vsep ppRho

instance Pretty VarInfo CompleteModule where
  pp env (Expanded em _ ) = pp env em
  pp env (KernelModule p) = do
    ppPhase <- pp env p
    pure $ text "⟨kernel module" <> text "@" <> ppPhase <> "⟩"

instance Pretty VarInfo Binding where
  pp _env (Binding b) = pure $ text "b" <> viaShow (hashUnique b)

instance Pretty VarInfo loc => Pretty VarInfo (BindingInfo loc) where
  pp env (BoundLocally loc) = do
    ppLoc <- pp env loc
    pure $ ppLoc <> text ":" <+> text "local"
  pp env (Defined loc) = do
    ppLoc <- pp env loc
    pure $ ppLoc <> text ":" <+> text "defined"
  pp env (Imported loc) = do
    ppLoc <- pp env loc
    pure $ ppLoc <> text ":" <+> text "import"

instance Pretty VarInfo EvalError where
  pp env (EvalErrorUnbound x) = do
    ppX <- pp env (Core (CoreVar x))
    pure $ text "Unbound:" <+> ppX
  pp _env (EvalErrorType (TypeError expected got)) =
    pure $ text "Expected a(n)" <+> text expected <+> "but got a(n)" <+> text got
  pp env (EvalErrorCase blame val) = do
    ppBlame <- pp env blame
    ppVal <- pp env val
    pure $ group $ hang 2 $ vsep [text "No case matched at" <+> ppBlame <> ":" , ppVal]
  pp env (EvalErrorUser (Syntax (Stx _ loc msg))) = do
    ppLoc <- pp env loc
    ppMsg <- pp env msg
    pure $ group $ hang 2 $ vsep [ppLoc <> ":", ppMsg]
  pp env (EvalErrorIdent v) = do
    ppV <- pp env v
    pure $ text "Attempt to bind identifier to non-value: " <+> ppV

instance Pretty VarInfo EvalResult where
  pp env (ExampleResult loc valEnv coreExpr sch val) = do
    let varEnv = fmap (const ()) valEnv
    ppLoc <- pp env loc
    ppCoreExpr <- pp varEnv coreExpr
    ppSch <- pp varEnv sch
    ppVal <- pp varEnv val
    pure $ group $ hang 2 $
      vsep [ text "Example at" <+> ppLoc <> text ":"
           , hang 2 $ group $
             vsep [ ppCoreExpr <+> text ":"
                  , ppSch
                  ] <+> text "↦"
           , ppVal
           ]
  pp _env (IOResult _) = pure $ text "IO action"

instance Pretty VarInfo BindingTable where
  pp env bs = do
    ppBindings <- for (HM.toList $ view bindings bs) $ \(name, triples) -> do
      ppName <- pp env name
      ppTriples <- for (F.toList triples) $ \(scs, b, info) -> do
        ppScs <- pp env scs
        ppB <- pp env b
        ppInfo <- pp env info
        pure $ ppScs <+> text "↦" <+> ppB <+> text "@" <+> ppInfo
      pure $ group $ hang 2 $ ppName <+> text "↦" <> line <> text "{" <> group (vsep ppTriples) <> text "}"
    pure $ group $ hang 2 $ vsep $ punc (text ",") ppBindings

punc :: Doc VarInfo -> [Doc VarInfo] -> [Doc VarInfo]
punc _ [] = []
punc _ [d] = [d]
punc doc (d1:d2:ds) = (d1 <> doc) : punc doc (d2:ds)

instance Pretty VarInfo Scope where
  pp _env = pure . viaShow

instance Pretty VarInfo ScopeSet where
  pp env scs = do
    let (allPhases, phases) = contents scs
    ppAllPhases <- ppSet allPhases
    ppPhases <- ppStore phases
    pure $ text "⟨" <> align (group (ppAllPhases <> text "," <> line <> ppPhases <> "⟩"))
    where
      commaSep = group . concatWith (\x y -> x <> text "," <> line <> y)
      ppSet :: Set Scope -> State Renumbering (Doc VarInfo)
      ppSet s = do
        ppS <- mapM (pp env) (Set.toList s)
        pure $ text "{" <> commaSep ppS <> text "}"
      
      ppStore :: Store Phase (Set Scope) -> State Renumbering (Doc VarInfo)
      ppStore m = do
        ppM <- for (St.toList m) $ \(p, scopes) -> do
          ppScopes <- ppSet scopes
          pure $ group (viaShow p <+> text "↦" <> line <> ppScopes)
        pure $ group (vsep ppM)

instance Pretty VarInfo KlisterPathError where
  pp _ = pure . ppKlisterPathError
