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
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text.Prettyprint.Doc hiding (Pretty(..), angles, parens)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc.Render.Text (putDoc, renderStrict)
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
pretty x = renderStrict (layoutPretty defaultLayoutOptions (pp Env.empty x))

prettyPrint :: Pretty ann a => a -> IO ()
prettyPrint x = putDoc (pp Env.empty x)

prettyPrintLn :: Pretty ann a => a -> IO ()
prettyPrintLn x = putDoc (pp Env.empty x) >> putStrLn ""

prettyEnv :: Pretty ann a => Env Var v -> a -> Text
prettyEnv env x =
  renderStrict (layoutPretty defaultLayoutOptions (pp (fmap (const ()) env) x))

prettyPrintEnv :: Pretty ann a => Env Var v -> a -> IO ()
prettyPrintEnv env x =
  putDoc (pp (fmap (const ()) env) x)


class Pretty ann a | a -> ann where
  pp :: Env Var () -> a -> Doc ann

instance Pretty ann (Doc ann) where
  pp _env doc = doc

data VarInfo
  = BindingSite Var
  | MacroBindingSite MacroVar
  | UseSite Var

instance Pretty VarInfo Core where
  pp env (Core e) = pp env e

instance (PrettyBinder VarInfo typePat, PrettyBinder VarInfo pat, Pretty VarInfo core) =>
         Pretty VarInfo (CoreF typePat pat core) where
  pp env (CoreVar v) =
    annotate (UseSite v) $
    case Env.lookupIdent v env of
      Nothing -> string ("!!" ++ show v ++ "!!")
      Just (Stx _ _ x) -> text x
  pp env (CoreLet x@(Stx _ _ y) v def body) =
    hang 2 $ group $
    vsep [ text "let" <+> hang 2 (group (vsep [ pp env y <+> text "="
                                              , pp env def
                                              ])) <+> text "in"
         , pp (env <> Env.singleton v x ()) body
         ]
  pp env (CoreLetFun f@(Stx _ _ g) fv x@(Stx _ _ y) v def body) =
    hang 2 $ group $
    vsep [ text "flet" <+>
           hang 2 (group (vsep [ pp env g <+> pp env y <+> text "="
                               , pp (env <> Env.singleton fv f () <> Env.singleton v x ()) def
                               ])) <+>
           text "in"
         , pp (env <> Env.singleton fv f ()) body
         ]
  pp env (CoreLam n@(Stx _ _ x) v body) =
    hang 2 $ group $
    text "λ" <> annotate (BindingSite v) (text x) <> "." <> line <>
    pp (env <> Env.singleton v n ()) body
  pp env (CoreApp fun arg) =
    hang 2 $ parens (pp env fun <> line <> pp env arg)
  pp env (CoreCtor ctor []) = pp env ctor
  pp env (CoreCtor ctor args) =
    hang 2 $ parens $ pp env ctor <+> group (vsep (map (pp env) args))
  pp env (CoreDataCase _ scrut cases) =
    hang 2 $ group $
    vsep [ text "case" <+> pp env scrut <+> "of"
         , encloseSep (flatAlt mempty (text "{" <> space))
                      (flatAlt mempty (space <> text "}"))
                      (flatAlt mempty (space <> text ";" <> space)) $
           map (\(pat, rhs) ->
                   let (ppPat, env') = ppBind env pat
                   in hang 2 $ group $
                      vsep [ppPat <+> text "↦",
                            pp (env <> env') rhs])
            cases
         ]
  pp _env (CoreString str) = text (T.pack (show str))
  pp env (CoreError what) =
    text "error" <+> pp env what
  pp env (CorePureMacro arg) =
    text "pure" <+> pp env arg
  pp env (CoreBindMacro act k) =
    hang 2 $ group (pp env act <+> text ">>=") <+> pp env k
  pp env (CoreSyntaxError err) =
    group $ text "syntax-error" <+> pp env err
  pp env (CoreIdentEq how e1 e2) =
    group $ text opName <+> pp env e1 <+> pp env e2
    where
      opName =
        case how of
          Free -> "free-identifier=?"
          Bound -> "bound-identifier=?"
  pp env (CoreLog msg) =
    group (hang 2 (vsep ["log", pp env msg]))
  pp _env CoreMakeIntroducer =
    text "make-introducer"
  pp _ CoreWhichProblem =
    text "which-problem"
  pp env (CoreSyntax stx) =
    pp env stx
  pp env (CoreCase _ scrut pats) =
    hang 2 $ group $
    group (hang 2 $ text "syntax-case" <+> pp env scrut <+> "of") <> line <>
    vsep [ parens $ hang 2 $
           let (b, env') = ppBind env pat
           in group (group (b <+> "=>") <> line <> pp (env <> env') body)
         | (pat, body) <- pats
         ]
  pp _env (CoreInteger s) = viaShow s
  pp env (CoreIdent x) = pp env x
  pp env (CoreEmpty e) = pp env e
  pp env (CoreCons e) = pp env e
  pp env (CoreList e) = pp env e
  pp env (CoreIntegerSyntax i) = pp env i
  pp env (CoreStringSyntax s) = pp env s
  pp env (CoreReplaceLoc loc stx) =
    group $ hang 2 $ vsep [ text "replace-loc"
                          , pp env loc
                          , pp env stx
                          ]
  pp env (CoreTypeCase _ scrut pats) =
    hang 2 $ group $
    group (hang 2 $ text "type-case" <+> pp env scrut <+> "of") <> line <>
    vsep [ parens $ hang 2 $
           let (b, env') = ppBind env pat
           in group (group (b <+> "=>") <> line <> pp (env <> env') body)
         | (pat, body) <- pats
         ]

instance Pretty VarInfo core => Pretty VarInfo (SyntaxError core) where
  pp env err =
    angles $
    pp env (view syntaxErrorMessage err) <> text ";" <+>
    concatWith (\d1 d2 -> d1 <> text "," <+> d2)
               (map (pp env) (view syntaxErrorLocations err))

class PrettyBinder ann a | a -> ann where
  ppBind :: Env Var () -> a -> (Doc ann, Env Var ())

instance PrettyBinder VarInfo a => PrettyBinder VarInfo (TyF a) where
  ppBind env t =
    let subs = ppBind env <$> t
    in (pp env (fst <$> subs), foldMap snd subs) 

newtype BinderPair = BinderPair (Ident, Var)

instance PrettyBinder VarInfo BinderPair where
  ppBind _env (BinderPair (ident@(Stx _ _ n), x)) =
    (annotate (BindingSite x) (text n), Env.singleton x ident ())

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
      [] -> (pp env ctor, Env.empty)
      _nonEmpty ->
        let subDocs = map (ppBind env) subPats
            env' = foldr (<>) Env.empty (map snd subDocs)
        in (pp env ctor <+> hsep (map fst subDocs),
            env')
  ppBind _env (PatternVar ident@(Stx _ _ n) x) =
    (annotate (BindingSite x) (text n), Env.singleton x ident ())

instance PrettyBinder VarInfo SyntaxPattern where
  ppBind _env (SyntaxPatternIdentifier ident@(Stx _ _ x) v) =
    (annotate (BindingSite v) (text x), Env.singleton v ident ())
  ppBind _env (SyntaxPatternInteger ident@(Stx _ _ x) v) =
    (parens $ text "integer" <+> annotate (BindingSite v) (text x), Env.singleton v ident ())
  ppBind _env (SyntaxPatternString ident@(Stx _ _ x) v) =
    (parens $ text "string" <+> annotate (BindingSite v) (text x), Env.singleton v ident ())
  ppBind _env SyntaxPatternEmpty =
    (text "()", Env.empty)
  ppBind _env (SyntaxPatternCons ida@(Stx _ _ xa) va idd@(Stx _ _ xd) vd) =
    (parens (text "cons" <+>
             annotate (BindingSite va) (text xa) <+>
             annotate (BindingSite vd) (text xd)),
     Env.insert vd idd () $ Env.singleton va ida ())
  ppBind _env (SyntaxPatternList vars) =
    (vec $
     hsep [annotate (BindingSite v) (text x)
          | (Stx _ _ x, v) <- vars
          ],
     foldr (\(x, v) e -> Env.insert x v () e) Env.empty [(v, x) | (x, v) <- vars])
  ppBind _env SyntaxPatternAny = (text "_", Env.empty)

instance Pretty VarInfo core => Pretty VarInfo (ScopedIdent core) where
  pp env ident =
    text "ident" <+>
    pp env (view scopedIdentIdentifier ident) <+>
    pp env (view scopedIdentScope ident)

instance Pretty VarInfo core => Pretty VarInfo (ScopedEmpty core) where
  pp env e =
    text "()" <> angles (pp env (view scopedEmptyScope e))

instance Pretty VarInfo core => Pretty VarInfo (ScopedCons core) where
  pp env pair =
    text "cons-from" <>
    parens (pp env (view scopedConsHead pair) <> text "," <+>
            pp env (view scopedConsTail pair)) <>
    angles (pp env (view scopedConsScope pair))

instance Pretty VarInfo core => Pretty VarInfo (ScopedList core) where
  pp env xs =
    vec (hsep $ map (pp env) (view scopedListElements xs)) <>
    angles (pp env (view scopedListScope xs))

instance Pretty VarInfo core => Pretty VarInfo (ScopedInteger core) where
  pp env s =
    pp env (view scopedInteger s) <>
    angles (pp env (view scopedIntegerScope s))

instance Pretty VarInfo core => Pretty VarInfo (ScopedString core) where
  pp env s =
    pp env (view scopedString s) <>
    angles (pp env (view scopedStringScope s))


instance PrettyBinder VarInfo CompleteDecl where
  ppBind env (CompleteDecl d) = ppBind env d

instance PrettyBinder VarInfo [CompleteDecl] where
  ppBind env decls = over _1 vsep
                   $ foldr go (\e -> (mempty, e)) decls mempty
    where
      go :: CompleteDecl
         -> (Env Var () -> ([Doc VarInfo], Env Var ()))
         -> (Env Var () -> ([Doc VarInfo], Env Var ()))
      go decl cc e = let (doc, e') = ppBind (env <> e) decl
                         (docs, e'') = cc (e <> e')
                     in (doc:docs, e'')


instance Pretty VarInfo Kind where
  pp _   KStar        = text "*"
  pp env (KFun k1 k2) = parens (pp env k1 <+> text "→" <+> pp env k2)
  pp _   (KMetaVar v) = text "META" <> viaShow v -- TODO make it look better

instance Pretty VarInfo (Scheme Ty) where
  pp env (Scheme [] t) =
    pp env t
  pp env (Scheme argKinds t) =
    text "∀" <>
    (align $ group $
     vsep [ group $
            vsep (zipWith ppArgKind typeVarNames argKinds) <> text "."
          , pp env t
          ])
    where
      ppArgKind varName kind = parens (text varName <+> text ":" <+> pp env kind)

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
  pp _   TSyntax        = text "Syntax"
  pp _   TInteger       = text "Integer"
  pp _   TString        = text "String"
  pp _   TOutputPort    = text "Output-Port"
  pp _   TFun           = text "(→)"
  pp _   TMacro         = text "Macro"
  pp _   TIO            = text "IO"
  pp _   TType          = text "Type"
  pp env (TDatatype t)  = pp env t
  pp _   (TSchemaVar n) = text $ typeVarNames !! fromIntegral n
  pp _   (TMetaVar v)   = text "META" <> viaShow v -- TODO

instance Pretty VarInfo a => Pretty VarInfo (TyF a) where
  pp _ (TyF TFun []) =
    parens (text "→")
  pp env (TyF TFun [a]) =
    parens (text "→" <+> pp env a)
  pp env (TyF TFun [a, b]) =
    parens $ align $ group $ vsep [pp env a <+> text "→", pp env b]
  pp env (TyF ctor args) =
    case args of
      [] -> pp env ctor
      more -> parens (align $ group $ pp env ctor <+> vsep (map (pp env) more))

instance Pretty VarInfo Datatype where
  pp _ d = text (view (datatypeName . datatypeNameText) d)

instance Pretty VarInfo Constructor where
  pp _ c = text (view (constructorName . constructorNameText) c)

instance Pretty VarInfo Ty where
  pp env (Ty t) = pp env t

instance (Pretty VarInfo s, Pretty VarInfo t, PrettyBinder VarInfo a, Pretty VarInfo b) =>
         PrettyBinder VarInfo (Decl t s a b) where
  ppBind env (Define n@(Stx _ _ x) v t e) =
    let env' = Env.singleton v n ()
    in (hang 4 $ group $
        vsep [ text "define" <+>
               annotate (BindingSite v) (text x) <+> text ":"
             , pp env t
             , text ":="
             , pp (env <> env') e
             ],
        env')
  ppBind env (DefineMacros macros) =
    (hang 4 $ text "define-macros" <> line <>
     vsep [hang 2 $ group $
           annotate (MacroBindingSite v) (text x) <+> text "↦" <> line <> pp env e -- TODO phase-specific binding environments in pprinter
          | (Stx _ _ x, v, e) <- macros
          ],
     mempty)
  ppBind env (Data (Stx _ _ x) _dn argKinds ctors) =
    (hang 2 $ group $
     vsep ( text "data" <+> text x <+>
            hsep [ parens (text α <+> ":" <+> pp env k)
                 | α <- typeVarNames
                 | k <- argKinds
                 ] <+>
            text "="
          : punc (space <> text "|")
            [ case args of
                [] -> text c
                more ->
                  hang 2 $
                  text c <+>
                  group (vsep [ pp env a | a <- more ])
            | (Stx _ _ c, _cn, args) <- ctors
            ]
          )
    , mempty)
  ppBind env (Meta d) =
    let (doc, env') = ppBind env d
    in (hang 4 $ text "meta" <> line <> doc, env')
  ppBind env (Import spec) =
    (hang 4 $ text "import" <+> pp env spec, mempty)
  ppBind env (Export x) =
    (hang 4 $ text "export" <+> pp env x, mempty)
  ppBind env (Example loc t e) =
    (hang 4 $
     text "example@" <> pp env loc <+>
     align (group (vsep [ group (pp env e) <+> text ":"
                        , pp env t
                        ])),
     mempty)
  ppBind env (Run _loc e) =
    (hang 4 $
     text "run" <+> align (pp env e),
     mempty)

instance Pretty VarInfo ExportSpec where
  pp env (ExportIdents ids) =
    text "{" <> align (vsep [pp env x | (Stx _ _ x) <- ids]) <> text "}"
  pp env (ExportRenamed spec rens) =
    align $ hang 2 $ group $
      pp env spec <> line <>
      text "renaming" <+> text "{" <>
      (align $ group $ vsep [text x <+> text "↦" <+> text y
                            | (x, y) <- rens
                            ]) <>
      text "}"
  pp env (ExportPrefixed spec p) =
    align $ hang 2 $ group $
    vsep [ text "(" <> align (group (pp env spec)) <> ")"
         , text "with" <+> text "prefix"
         , text p
         ]
  pp env (ExportShifted spec i) =
    align $ hang 2 $ group $
    vsep [ text "(" <> align (group (pp env spec)) <> ")"
         , text "shifted" <+> text "by"
         , viaShow i
         ]

instance Pretty VarInfo ImportSpec where
  pp env (ImportModule mn) = pp env mn
  pp env (ImportOnly spec ids) = group $ vsep [ text "only"
                                              , pp env spec
                                              , parens (group (vsep (map (pp env) ids)))
                                              ]
  pp env (ShiftImports spec i) = pp env spec <+> "⇑" <+> viaShow i
  pp env (RenameImports spec rens) = group $ vsep [ text "rename"
                                                  , pp env spec
                                                  , group (vsep [pp env x <+> pp env y | (x, y) <- rens])
                                                  ]
  pp env (PrefixImports spec pref) = group $ vsep [ text "prefix"
                                                  , pp env spec
                                                  , viaShow pref
                                                  ]

instance Pretty VarInfo ModuleName where
  pp _ n = text (moduleNameText n)

instance (Functor f, Traversable f, PrettyBinder VarInfo a) => Pretty VarInfo (Module f a) where
  pp env m =
    hang 4 $
    text "module" <+> pp env (view moduleName m) <> line <>
    concatWith terpri (fst (runState (traverse go (view moduleBody m)) env))

    where
      terpri d1 d2 = d1 <> line <> d2
      go :: a -> State (Env Var ()) (Doc VarInfo)
      go d =
        do thisEnv <- get
           let (doc, newEnv) = ppBind thisEnv d
           put (thisEnv <> newEnv)
           return doc

instance Pretty VarInfo SrcLoc where
  pp env loc =
    string (takeFileName (view srcLocFilePath loc)) <> text ":" <>
    pp env (view srcLocStart loc) <> text "-" <>
    pp env (view srcLocEnd loc)

instance Pretty VarInfo SrcPos where
  pp _env pos =
    viaShow (view srcPosLine pos) <> text "." <>
    viaShow (view srcPosCol pos)

instance Pretty VarInfo a => Pretty VarInfo (Stx a) where
  pp env (Stx _ loc v) =
    text "#" <>
    (align . group)
      (text "[" <> pp env loc <> text "]" <> line' <> text "<" <>
       align (pp env v) <>
       text ">")

instance Pretty VarInfo Syntax where
  pp env (Syntax e) = pp env e

instance Pretty VarInfo (ExprF Syntax) where
  pp _   (Id x)      = text x
  pp _   (String s)  = viaShow s
  pp _   (Integer s) = viaShow s
  pp env (List xs)   = parens (group (vsep (map (pp env . syntaxE) xs)))

instance Pretty VarInfo Closure where
  pp _ _ = text "#<closure>"

instance Pretty VarInfo Value where
  pp env (ValueClosure c) = pp env c
  pp env (ValueSyntax stx) = pp env stx
  pp env (ValueMacroAction act) = pp env act
  pp _env (ValueIOAction _) = "#<IO action>"
  pp _env (ValueOutputPort _) = "#<output port>"
  pp _env (ValueInteger s) = viaShow s
  pp _env (ValueCtor c []) =
    parens $
    text (view (constructorName . constructorNameText) c)
  pp env (ValueCtor c args) =
    parens $
    text (view (constructorName . constructorNameText) c) <+>
    align (group (vsep (map (pp env) args)))
  pp _env (ValueType ptr) = text "#t<" <> viaShow ptr <> text ">"
  pp _env (ValueString str) = text (T.pack (show str))

instance Pretty VarInfo MacroAction where
  pp env (MacroActionPure v) =
    text "pure" <+> pp env v
  pp env (MacroActionBind v k) =
    group $
      group (pp env v <> line <> text ">>=") <> line <>
      pp env k
  pp env (MacroActionSyntaxError err) =
    text "syntax-error" <+> pp env err
  pp env (MacroActionIdentEq how v1 v2) =
    group $ parens $ vsep [text opName, pp env v1, pp env v2]
    where
      opName =
        case how of
          Free  -> "free-identifier=?"
          Bound -> "bound-identifier=?"
  pp env (MacroActionLog stx) =
    hang 2 $ group $ vsep [text "log", pp env stx]
  pp _env MacroActionIntroducer =
    text "make-introducer"
  pp _env MacroActionWhichProblem =
    text "which-problem"
  pp env (MacroActionTypeCase venv _loc ptr cases) =
    hang 2 $
    text "type-case" <+> text "#t<" <> viaShow ptr <> text ">" <+> text "of" <> line <>
    vsep (map ppCase cases)
    where
      ppCase (pat, c) =
        let (patDoc, env') = ppBind env pat
        in hang 2 $ group $ vsep [patDoc <+> "↦", pp (fmap (const ()) venv <> env') c]

instance Pretty VarInfo Phase where
  pp _env p = text "p" <> viaShow (phaseNum p)

instance Pretty VarInfo a => Pretty VarInfo (World a) where
  pp env w =
    vsep $ map (hang 4)
      [vsep [ text "Expanded modules"
            , vsep [ pp env m
                   | (_, m) <- Map.toList (view worldModules w)
                   ]
            ]
      , vsep [ text "Modules visited"
             , vsep [ hang 4 $
                      pp env mn <> line <>
                      text "{" <> group (vsep (map (pp env) ps)) <> text "}"
                    | (mn, Set.toList -> ps) <- Map.toList (view worldVisited w)
                    ]
             ]
      , vsep [ text "Environments"
             , hang 4 $
               vsep [ hang 4 $
                      pp env p <> line <>
                      pp env rho
                    | (p, rho) <- Map.toList $ view worldEnvironments w
                    ]
             ]
      ]

instance Pretty VarInfo Text where
  pp _ = text

instance Pretty VarInfo a => Pretty VarInfo (Env Var a) where
  pp env rho =
    vsep [ hang 4 $ viaShow x <+> pp env n <> line <> pp env v
         | (x, n, v) <- Env.toList rho
         ]

instance Pretty VarInfo a => Pretty VarInfo (Env MacroVar a) where
  pp env rho =
    vsep [ hang 4 $ viaShow x <+> pp env n <> line <> pp env v
         | (x, n, v) <- Env.toList rho
         ]

instance Pretty VarInfo CompleteModule where
  pp env (Expanded em _ ) = pp env em
  pp env (KernelModule p) = text "⟨kernel module" <> text "@" <> pp env p <> "⟩"

instance Pretty VarInfo Binding where
  pp _env (Binding b) = text "b" <> viaShow (hashUnique b)

instance Pretty VarInfo loc => Pretty VarInfo (BindingInfo loc) where
  pp env (BoundLocally loc) = pp env loc <> text ":" <+> text "local"
  pp env (Defined loc) = pp env loc <> text ":" <+> text "defined"
  pp env (Imported loc) = pp env loc <> text ":" <+> text "import"

instance Pretty VarInfo EvalError where
  pp env (EvalErrorUnbound x) = text "Unbound:" <+> pp env (Core (CoreVar x))
  pp _env (EvalErrorType (TypeError expected got)) =
    text "Expected a(n)" <+> text expected <+> "but got a(n)" <+> text got
  pp env (EvalErrorCase blame val) =
    group $ hang 2 $ vsep [text "No case matched at" <+> pp env blame <> ":" , pp env val]
  pp env (EvalErrorUser (Syntax (Stx _ loc msg))) =
    group $ hang 2 $ vsep [pp env loc <> ":", pp env msg]

instance Pretty VarInfo EvalResult where
  pp env (ExampleResult loc valEnv coreExpr sch val) =
    let varEnv = fmap (const ()) valEnv
    in group $ hang 2 $
       vsep [ text "Example at" <+> pp env loc <> text ":"
            , hang 2 $ group $
              vsep [ pp varEnv coreExpr <+> text ":"
                   , pp varEnv sch
                   ] <+> text "↦"
            , pp varEnv val
            ]
  pp _env (IOResult _) = text "IO action"


instance Pretty VarInfo BindingTable where
  pp env bs =
    group $ hang 2 $ vsep $
    punc (text ",") [ group $ hang 2 $
                      pp env n <+> text "↦" <> line <>
                      text "{" <> group (vsep [ pp env scs <+> text "↦" <+>
                                                pp env b <+> text "@" <+>
                                                pp env info
                                              | (scs, b, info) <- xs]) <> text "}"
                    | (n, xs) <- Map.toList $ view bindings bs
                    ]

punc :: Doc VarInfo -> [Doc VarInfo] -> [Doc VarInfo]
punc _ [] = []
punc _ [d] = [d]
punc doc (d1:d2:ds) = (d1 <> doc) : punc doc (d2:ds)

instance Pretty VarInfo Scope where
  pp _env = viaShow

instance Pretty VarInfo ScopeSet where
  pp env scs =
    let (allPhases, phases) = contents scs
    in text "⟨" <> align (group (ppSet allPhases <> text "," <> line <> ppMap (ppSet <$> phases) <> "⟩"))

    where
      commaSep = group . concatWith (\x y -> x <> text "," <> line <> y)
      ppSet s =
        text "{" <> commaSep (map (pp env) (Set.toList s)) <> text "}"
      ppMap m =
        group (vsep [group (viaShow k <+> text "↦" <> line <> v) | (k, v) <- Map.toList m])


instance Pretty VarInfo KlisterPathError where
  pp _ = ppKlisterPathError
