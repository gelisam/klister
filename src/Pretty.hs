{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Pretty (Pretty(..), pretty, prettyPrint, prettyEnv, prettyPrintEnv) where

import Control.Lens
import Control.Monad.State
import Data.Text.Prettyprint.Doc hiding (Pretty(..), angles, parens)
import Data.Text (Text)
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc.Render.Text (putDoc, renderStrict)

import Core
import Env
import Module
import ShortShow
import Syntax

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
    hang 2 $
    text "λ" <> annotate (BindingSite v) (text x) <> "." <+>
    pp (env <> Env.singleton v n ()) body
  pp env (CoreApp fun arg) =
    hang 2 $ parens (pp env fun <+> pp env arg)
  pp env (CorePure arg) =
    text "pure" <+> pp env arg
  pp env (CoreBind act k) =
    hang 2 $ group (pp env act <+> text ">>=") <+> pp env k
  pp env (CoreSyntaxError err) =
    group $ text "syntax-error" <+> pp env err
  pp env (CoreSendSignal arg) =
    group $ text "send-signal" <+> pp env arg
  pp _env (CoreSyntax stx) =
    string (shortShow stx) -- TODO pp stx object
  pp env (CoreCase scrut pats) =
    hang 2 $ group $
    group (hang 2 $ text "syntax-case" <+> pp env scrut <+> "of") <> line <>
    vsep [ parens $ hang 2 $
           let (b, env') = ppBind env pat
           in group (b <+> "=>") <+> pp (env <> env') body
         | (pat, body) <- pats
         ]
  pp _env (CoreIdentifier x) = viaShow x
  pp _env (CoreSignal s) = viaShow s
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

instance Pretty VarInfo a => PrettyBinder VarInfo (Decl a) where
  ppBind env (Define n@(Stx _ _ x) v e) =
    let env' = Env.singleton v n ()
    in (hang 4 $ group $
        text "define" <+> annotate (BindingSite v) (text x) <+> text ":=" <> line <>
        pp (env <> env') e,
        env')
  ppBind env (DefineMacros macros) =
    (text "define-macros" <> line <>
     vsep [text x <+> text "↦" <+> pp env e -- TODO phase-specific binding environments in pprinter
          | (Stx _ _ x, e) <- macros
          ],
     mempty)
  ppBind env (Meta d) =
    let (doc, env') = ppBind env d
    in (hang 4 $ text "meta" <> line <> doc, env')
  ppBind env (Example e) = (hang 4 $ text "example" <+> group (pp env e), mempty)

instance Pretty VarInfo ModuleName where
  pp _ (ModuleName n) = viaShow n

instance (Functor f, Traversable f, PrettyBinder VarInfo a) => Pretty VarInfo (Module f a) where
  pp env m =
    hang 4 $
    text "module" <> pp env (view moduleName m) <> line <>
    concatWith terpri (fst (runState (traverse go (view moduleBody m)) env))

    where
      terpri d1 d2 = d1 <> line <> d2
      go :: a -> State (Env ()) (Doc VarInfo)
      go d =
        do thisEnv <- get
           let (doc, newEnv) = ppBind thisEnv d
           put (thisEnv <> newEnv)
           return doc
