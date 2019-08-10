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
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc.Render.Text (putDoc, renderStrict)

import Core
import Env
import Module
import ModuleName
import Phase
import Scope
import ScopeSet
import Syntax
import Syntax.SrcLoc
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

prettyEnv :: Pretty ann a => Env v -> a -> Text
prettyEnv env x =
  renderStrict (layoutPretty defaultLayoutOptions (pp (fmap (const ()) env) x))

prettyPrintEnv :: Pretty ann a => Env v -> a -> IO ()
prettyPrintEnv env x =
  putDoc (pp (fmap (const ()) env) x)


class Pretty ann a | a -> ann where
  pp :: Env () -> a -> Doc ann

data VarInfo
  = BindingSite Var
  | UseSite Var

instance Pretty VarInfo Core where
  pp env (Core e) = pp env e

instance Pretty VarInfo core => Pretty VarInfo (CoreF core) where
  pp env (CoreVar v) =
    annotate (UseSite v) $
    case Env.lookupIdent v env of
      Nothing -> string ("!!" ++ show v ++ "!!")
      Just (Stx _ _ x) -> text x
  pp env (CoreLam n@(Stx _ _ x) v body) =
    hang 2 $ group $
    text "λ" <> annotate (BindingSite v) (text x) <> "." <> line <>
    pp (env <> Env.singleton v n ()) body
  pp env (CoreApp fun arg) =
    hang 2 $ parens (pp env fun <> line <> pp env arg)
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
  pp env (CoreVec e) = pp env e

instance Pretty VarInfo core => Pretty VarInfo (SyntaxError core) where
  pp env err =
    angles $
    pp env (view syntaxErrorMessage err) <> text ";" <+>
    concatWith (\d1 d2 -> d1 <> text "," <+> d2)
               (map (pp env) (view syntaxErrorLocations err))

class PrettyBinder ann a | a -> ann where
  ppBind :: Env () -> a -> (Doc ann, Env ())

instance PrettyBinder VarInfo Pattern where
  ppBind _env (PatternIdentifier ident@(Stx _ _ x) v) =
    (annotate (BindingSite v) (text x), Env.singleton v ident ())
  ppBind _env PatternEmpty =
    (text "()", Env.empty)
  ppBind _env (PatternCons ida@(Stx _ _ xa) va idd@(Stx _ _ xd) vd) =
    (parens (text "cons" <+>
             annotate (BindingSite va) (text xa) <+>
             annotate (BindingSite vd) (text xd)),
     Env.insert vd idd () $ Env.singleton va ida ())
  ppBind _env (PatternVec vars) =
    (vec $
     hsep [annotate (BindingSite v) (text x)
          | (Stx _ _ x, v) <- vars
          ],
     foldr (\(x, v) e -> Env.insert x v () e) Env.empty [(v, x) | (x, v) <- vars])

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

instance Pretty VarInfo core => Pretty VarInfo (ScopedVec core) where
  pp env xs =
    vec (hsep $ map (pp env) (view scopedVecElements xs)) <>
    angles (pp env (view scopedVecScope xs))

instance PrettyBinder VarInfo CompleteDecl where
  ppBind env (CompleteDecl d) = ppBind env d

instance (PrettyBinder VarInfo a, Pretty VarInfo b) => PrettyBinder VarInfo (Decl a b) where
  ppBind env (Define n@(Stx _ _ x) v e) =
    let env' = Env.singleton v n ()
    in (hang 4 $ group $
        text "define" <+> annotate (BindingSite v) (text x) <+> text ":=" <> line <>
        pp (env <> env') e,
        env')
  ppBind env (DefineMacros macros) =
    (hang 4 $ text "define-macros" <> line <>
     vsep [hang 2 $ group $
           text x <+> text "↦" <> line <> pp env e -- TODO phase-specific binding environments in pprinter
          | (Stx _ _ x, e) <- macros
          ],
     mempty)
  ppBind env (Meta d) =
    let (doc, env') = ppBind env d
    in (hang 4 $ text "meta" <> line <> doc, env')
  ppBind env (Import spec) =
    (hang 4 $ text "import" <+> pp env spec, mempty)
  ppBind env (Export x) =
    (hang 4 $ text "export" <+> pp env x, mempty)
  ppBind env (Example e) = (hang 4 $ text "example" <+> group (pp env e), mempty)

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
      go :: a -> State (Env ()) (Doc VarInfo)
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
    text "#[" <> pp env loc <> "]<" <>
    align (pp env v) <>
    text ">"

instance Pretty VarInfo Syntax where
  pp env (Syntax e) = pp env e

instance Pretty VarInfo (ExprF Syntax) where
  pp _   (Id x)     = text x
  pp _   (String s) = viaShow s
  pp _   (Sig s)    = viaShow s
  pp _   (Bool b)   = text $ if b then "#true" else "#false"
  pp env (List xs)  = parens (group (vsep (map (pp env . syntaxE) xs)))
  pp env (Vec xs)   = brackets (group (vsep (map (pp env . syntaxE) xs)))

instance Pretty VarInfo Closure where
  pp _ _ = text "#<closure>"

instance Pretty VarInfo Value where
  pp env (ValueClosure c) = pp env c
  pp env (ValueSyntax stx) = pp env stx
  pp env (ValueMacroAction act) = pp env act
  pp _env (ValueSignal s) = viaShow s
  pp _env (ValueBool b) = text $ if b then "#true" else "#false"

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

instance Pretty VarInfo Phase where
  pp = const viaShow

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

instance Pretty VarInfo a => Pretty VarInfo (Env a) where
  pp env rho =
    vsep [ hang 4 $ viaShow x <+> pp env n <> line <> pp env v
         | (x, n, v) <- Env.toList rho
         ]

instance Pretty VarInfo CompleteModule where
  pp env (Expanded em) = pp env em
  pp env (KernelModule p) = text "⟨kernel module" <> text "@" <> pp env p <> "⟩"

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
