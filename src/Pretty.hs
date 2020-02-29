{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Pretty (Pretty(..), string, text, viaShow, (<+>), (<>), hang, line, group, vsep, hsep, VarInfo(..), pretty, prettyPrint, prettyPrintLn, prettyEnv, prettyPrintEnv) where

import Control.Lens hiding (List)
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text.Prettyprint.Doc hiding (Pretty(..), angles, parens)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc.Render.Text (putDoc, renderStrict)
import Data.Unique

import Binding
import Binding.Info
import Core
import Datatype
import Env
import Module
import ModuleName
import Phase
import Scope
import ScopeSet
import Syntax
import Syntax.SrcLoc
import Type
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

data VarInfo
  = BindingSite Var
  | MacroBindingSite MacroVar
  | UseSite Var

instance Pretty VarInfo Core where
  pp env (Core e) = pp env e

instance Pretty VarInfo core => Pretty VarInfo (CoreF core) where
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
  pp env (CoreDataCase scrut cases) =
    hang 2 $ vsep (text "case" <+> pp env scrut <+> "of" :
                   [ group $ hang 2 $ vsep [ ppat <+> text "↦", pp (env <> env') rhs]
                   | (pat, rhs) <- cases
                   , let (ppat, env') = ppBind env pat
                   ])
  pp env (CorePure arg) =
    text "pure" <+> pp env arg
  pp env (CoreBind act k) =
    hang 2 $ group (pp env act <+> text ">>=") <+> pp env k
  pp env (CoreSyntaxError err) =
    group $ text "syntax-error" <+> pp env err
  pp env (CoreSendSignal arg) =
    group $ text "send-signal" <+> pp env arg
  pp env (CoreWaitSignal arg) =
    group $ text "wait-signal" <+> pp env arg
  pp env (CoreIdentEq how e1 e2) =
    group $ text opName <+> pp env e1 <+> pp env e2
    where
      opName =
        case how of
          Free -> "free-identifier=?"
          Bound -> "bound-identifier=?"
  pp env (CoreLog msg) =
    group (hang 2 (vsep ["log", pp env msg]))
  pp env (CoreSyntax stx) =
    pp env stx
  pp env (CoreCase scrut pats) =
    hang 2 $ group $
    group (hang 2 $ text "syntax-case" <+> pp env scrut <+> "of") <> line <>
    vsep [ parens $ hang 2 $
           let (b, env') = ppBind env pat
           in group (group (b <+> "=>") <> line <> pp (env <> env') body)
         | (pat, body) <- pats
         ]
  pp _env (CoreIdentifier x) = viaShow x
  pp _env (CoreSignal s) = viaShow s
  pp _env (CoreBool b) = text $ if b then "#true" else "#false"
  pp env (CoreIf b t f) =
    group $ hang 2 $
    group (text "if" <+> pp env b) <> line <>
    group (text "then" <+> pp env t) <> line <>
    group (text "else" <+> pp env f)
  pp env (CoreIdent x) = pp env x
  pp env (CoreEmpty e) = pp env e
  pp env (CoreCons e) = pp env e
  pp env (CoreList e) = pp env e
  pp env (CoreReplaceLoc loc stx) =
    group $ hang 2 $ vsep [ text "replace-loc"
                          , pp env loc
                          , pp env stx
                          ]

instance Pretty VarInfo core => Pretty VarInfo (SyntaxError core) where
  pp env err =
    angles $
    pp env (view syntaxErrorMessage err) <> text ";" <+>
    concatWith (\d1 d2 -> d1 <> text "," <+> d2)
               (map (pp env) (view syntaxErrorLocations err))

class PrettyBinder ann a | a -> ann where
  ppBind :: Env Var () -> a -> (Doc ann, Env Var ())

instance PrettyBinder VarInfo ConstructorPattern where
  ppBind env (ConstructorPattern ctor vars) =
    case vars of
      [] -> (pp env ctor, Env.empty)
      more -> ( hang 2 $
                pp env ctor <+>
                hsep [ annotate (BindingSite v) (text x)
                     | (Stx _ _ x, v) <- more
                     ]
              , foldr (\(x, v) e -> Env.insert x v () e) Env.empty [(v, x) | (x, v) <- more]
              )
  ppBind _env (AnyConstructor ident@(Stx _ _ n) x) =
    (annotate (BindingSite x) (text n), Env.singleton x ident ())

instance PrettyBinder VarInfo SyntaxPattern where
  ppBind _env (SyntaxPatternIdentifier ident@(Stx _ _ x) v) =
    (annotate (BindingSite v) (text x), Env.singleton v ident ())
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

instance PrettyBinder VarInfo CompleteDecl where
  ppBind env (CompleteDecl d) = ppBind env d

instance Pretty VarInfo (Scheme Ty) where
  pp env (Scheme 0 t) =
    pp env t
  pp env (Scheme n t) =
    text "∀" <>
    (align $ group $
     vsep [ group $
            vsep (map text (take (fromIntegral n) typeVarNames)) <> text "."
          , pp env t
          ])

typeVarNames :: [Text]
typeVarNames = [ T.pack base <> T.pack (show i)
               | (base, i) <- greek
               ]
  where
    greek = [ ([base], num)
        | num <- [(0 :: Integer)..]
        , base <- "αβγδεζηθικλμνξοπρστυφχψω"
        ]


instance Pretty VarInfo a => Pretty VarInfo (TyF a) where
  pp _ TUnit = text "Unit"
  pp _ TBool = text "Bool"
  pp _ TSyntax = text "Syntax"
  pp _ TSignal = text "Signal"
  pp env (TFun a b) =
    parens $ align $ group $ vsep [pp env a <+> text "→", pp env b]
  pp env (TMacro a) = parens (text "Macro" <+> align (pp env a))
  pp env (TDatatype t args) =
    case args of
      [] -> pp env t
      more -> parens (align $ group $ pp env t <+> vsep (map (pp env) more))
  pp _ (TSchemaVar n) = text $ typeVarNames !! fromIntegral n
  pp _ (TMetaVar v) = text "META" <> viaShow v -- TODO

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
  ppBind env (Data (Stx _ _ x) _dn arity ctors) =
    (hang 2 $ group $
     vsep ( text "data" <+> text x <+>
            hsep [ text α
                 | α <- take (fromIntegral arity) typeVarNames
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
  ppBind env (Example t e) =
    (hang 4 $
     text "example" <+>
     align (group (vsep [ group (pp env e) <+> text ":"
                        , pp env t
                        ])),
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
  pp _ n = viaShow (moduleNameText n)

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
    string (view srcLocFilePath loc) <> text ":" <>
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
  pp _   (Id x)     = text x
  pp _   (String s) = viaShow s
  pp _   (Sig s)    = viaShow s
  pp _   (Bool b)   = text $ if b then "#true" else "#false"
  pp env (List xs)  = parens (group (vsep (map (pp env . syntaxE) xs)))

instance Pretty VarInfo Closure where
  pp _ _ = text "#<closure>"

instance Pretty VarInfo Value where
  pp env (ValueClosure c) = pp env c
  pp env (ValueSyntax stx) = pp env stx
  pp env (ValueMacroAction act) = pp env act
  pp _env (ValueSignal s) = viaShow s
  pp _env (ValueBool b) = text $ if b then "#true" else "#false"
  pp env (ValueCtor c args) =
    text (view (constructorName . constructorNameText) c) <+>
    align (group (vsep (map (pp env) args)))

instance Pretty VarInfo MacroAction where
  pp env (MacroActionPure v) =
    text "pure" <+> pp env v
  pp env (MacroActionBind v k) =
    group (group (pp env v <> line <> text ">>=") <> line <> pp env k)
  pp env (MacroActionSyntaxError err) =
    text "syntax-error" <+> pp env err
  pp _env (MacroActionSendSignal s) =
    text "send-signal" <+> viaShow s
  pp _env (MacroActionWaitSignal s) =
    text "wait-signal" <+> viaShow s
  pp env (MacroActionIdentEq how v1 v2) =
    group $ parens $ vsep [text opName, pp env v1, pp env v2]
    where
      opName =
        case how of
          Free  -> "free-identifier=?"
          Bound -> "bound-identifier=?"
  pp env (MacroActionLog stx) =
    hang 2 $ group $ vsep [text "log", pp env stx]

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

