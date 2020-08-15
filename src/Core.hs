{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
module Core where

import Control.Lens hiding (elements)
import Control.Monad
import Data.Bifunctor.TH
import Data.List
import Data.Foldable
import Data.Text (Text)
import Data.Traversable

import Alpha
import Datatype
import ModuleName
import Phase
import ShortShow
import Signals
import Syntax
import Syntax.SrcLoc
import Type
import Unique


data SyntaxError a = SyntaxError
  { _syntaxErrorLocations :: [a]
  , _syntaxErrorMessage   :: a
  }
  deriving (Eq, Functor, Foldable, Show, Traversable)
makeLenses ''SyntaxError

newtype Var = Var Unique
  deriving (AlphaEq, Eq, Ord)

instance Show Var where
  show (Var i) = "(Var " ++ show (hashUnique i) ++ ")"

newtype MacroVar = MacroVar Unique
  deriving (AlphaEq, Eq, Ord)

instance Show MacroVar where
  show (MacroVar i) = "(MacroVar " ++ show (hashUnique i) ++ ")"

data TypePattern
  = TypePattern (TyF (Ident, Var))
  | AnyType Ident Var
  deriving (Eq, Show)

data ConstructorPattern
  = ConstructorPattern !Constructor [(Ident, Var)]
  | AnyConstructor Ident Var
  deriving (Eq, Show)
makePrisms ''ConstructorPattern

instance Phased ConstructorPattern where
  shift _ = id

instance Phased TypePattern where
  shift _ = id

data SyntaxPattern
  = SyntaxPatternIdentifier Ident Var
  | SyntaxPatternEmpty
  | SyntaxPatternCons Ident Var Ident Var
  | SyntaxPatternList [(Ident, Var)]
  | SyntaxPatternAny
  deriving (Eq, Show)
makePrisms ''SyntaxPattern

data ScopedIdent core = ScopedIdent
  { _scopedIdentIdentifier :: core
  , _scopedIdentScope      :: core
  }
  deriving (Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedIdent

data ScopedEmpty core = ScopedEmpty
  { _scopedEmptyScope :: core
  }
  deriving (Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedEmpty

data ScopedCons core = ScopedCons
  { _scopedConsHead  :: core
  , _scopedConsTail  :: core
  , _scopedConsScope :: core
  }
  deriving (Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedCons

data ScopedList core = ScopedList
  { _scopedListElements :: [core]
  , _scopedListScope    :: core
  }
  deriving (Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedList

data HowEq = Free | Bound
  deriving (Eq, Show)

data CoreF typePat pat core
  = CoreVar Var
  | CoreLet Ident Var core core
  | CoreLetFun Ident Var Ident Var core core
  | CoreLam Ident Var core
  | CoreApp core core
  | CoreCtor Constructor [core] -- ^ Constructor application
  | CoreDataCase SrcLoc core [(pat, core)]
  | CoreError core
  | CorePure core                       -- :: a -> Macro a
  | CoreBind core core                  -- :: Macro a -> (a -> Macro b) -> Macro b
  | CoreSyntaxError (SyntaxError core)  -- :: Macro a
  | CoreSendSignal core                 -- :: Signal -> Macro ()
  | CoreWaitSignal core                 -- :: Signal -> Macro ()
  | CoreIdentEq HowEq core core         -- bound-identifier=? :: Syntax -> Syntax -> Macro Bool
                                        -- free-identifier=?  :: Syntax -> Syntax -> Macro Bool
  | CoreLog core
  | CoreMakeIntroducer
  | CoreWhichProblem
  | CoreSyntax Syntax
  | CoreCase SrcLoc core [(SyntaxPattern, core)]
  | CoreIdentifier Ident
  | CoreSignal Signal
  | CoreIdent (ScopedIdent core)
  | CoreEmpty (ScopedEmpty core)
  | CoreCons (ScopedCons core)
  | CoreList (ScopedList core)
  | CoreReplaceLoc core core
  | CoreTypeCase SrcLoc core [(typePat, core)]
  deriving (Eq, Functor, Foldable, Show, Traversable)
makePrisms ''CoreF
deriveBifunctor ''CoreF
deriveBifoldable ''CoreF
deriveBitraversable ''CoreF

mapCoreF ::
  (a -> b) -> (c -> d) -> (e -> f) ->
  CoreF a c e ->
  CoreF b d f
mapCoreF _f _g _h (CoreVar x) =
  CoreVar x
mapCoreF _f _g h (CoreLet n x def body) =
  CoreLet n x (h def) (h body)
mapCoreF _f _g h (CoreLetFun funN funX n x def body) =
  CoreLetFun funN funX n x (h def) (h body)
mapCoreF _f _g h (CoreLam n x body) =
  CoreLam n x (h body)
mapCoreF _f _g h (CoreApp rator rand) =
  CoreApp (h rator) (h rand)
mapCoreF _f _g h (CoreCtor ctor args) =
  CoreCtor ctor (map h args)
mapCoreF _f g h (CoreDataCase loc scrut cases) =
  CoreDataCase loc (h scrut) [(g pat, h c) | (pat, c) <- cases]
mapCoreF _f _g h (CoreError msg) =
  CoreError (h msg)
mapCoreF _f _g h (CorePure core) =
  CorePure (h core)
mapCoreF _f _g h (CoreBind act k) =
  CoreBind (h act) (h k)
mapCoreF _f _g h (CoreSyntaxError err) =
  CoreSyntaxError (fmap h err)
mapCoreF _f _g h (CoreSendSignal core) =
  CoreSendSignal (h core)
mapCoreF _f _g h (CoreWaitSignal core) =
  CoreWaitSignal (h core)
mapCoreF _f _g h (CoreIdentEq how l r) =
  CoreIdentEq how (h l) (h r)
mapCoreF _f _g h (CoreLog core) =
  CoreLog (h core)
mapCoreF _f _g _h CoreMakeIntroducer =
  CoreMakeIntroducer
mapCoreF _f _g _h CoreWhichProblem =
  CoreWhichProblem
mapCoreF _f _g _h (CoreSyntax stx) =
  CoreSyntax stx
mapCoreF _f _g h (CoreCase loc scrut cases) =
  CoreCase loc (h scrut) [(pat, h c) | (pat, c) <- cases]
mapCoreF _f _g _h (CoreIdentifier n) =
  CoreIdentifier n
mapCoreF _f _g _h (CoreSignal s) =
  CoreSignal s
mapCoreF _f _g h (CoreIdent ident) =
  CoreIdent (fmap h ident)
mapCoreF _f _g h (CoreEmpty args) =
  CoreEmpty (fmap h args)
mapCoreF _f _g h (CoreCons args) =
  CoreCons (fmap h args)
mapCoreF _f _g h (CoreList args) =
  CoreList (fmap h args)
mapCoreF _f _g h (CoreReplaceLoc src dest) =
  CoreReplaceLoc (h src) (h dest)
mapCoreF f _g h (CoreTypeCase loc scrut cases) =
  CoreTypeCase loc (h scrut) [(f pat, h c) | (pat, c) <- cases]

traverseCoreF :: Applicative f => (a -> f d) -> (b -> f e) -> (c -> f g) -> CoreF a b c -> f (CoreF d e g)
traverseCoreF _f _g _h (CoreVar x) =
  pure $ CoreVar x
traverseCoreF _f _g h (CoreLet n x def body) =
  CoreLet n x <$> h def <*> h body
traverseCoreF _f _g h (CoreLetFun funN funX n x def body) =
  CoreLetFun funN funX n x <$> h def <*> h body
traverseCoreF _f _g h (CoreLam n x body) =
  CoreLam n x <$> h body
traverseCoreF _f _g h (CoreApp rator rand) =
  CoreApp <$> h rator <*> h rand
traverseCoreF _f _g h (CoreCtor ctor args) =
  CoreCtor ctor <$> traverse h args
traverseCoreF _f g h (CoreDataCase loc scrut cases) =
  CoreDataCase loc <$> h scrut <*> for cases \ (pat, c) -> (,) <$> g pat <*> h c
traverseCoreF _f _g h (CoreError msg) =
  CoreError <$> h msg
traverseCoreF _f _g h (CorePure core) =
  CorePure <$> h core
traverseCoreF _f _g h (CoreBind act k) =
  CoreBind <$> h act <*> h k
traverseCoreF _f _g h (CoreSyntaxError err) =
  CoreSyntaxError <$> traverse h err
traverseCoreF _f _g h (CoreSendSignal core) =
  CoreSendSignal <$> h core
traverseCoreF _f _g h (CoreWaitSignal core) =
  CoreWaitSignal <$> h core
traverseCoreF _f _g h (CoreIdentEq how l r) =
  CoreIdentEq how <$> h l <*> h r
traverseCoreF _f _g h (CoreLog core) =
  CoreLog <$> h core
traverseCoreF _f _g _h CoreMakeIntroducer =
  pure CoreMakeIntroducer
traverseCoreF _f _g _h CoreWhichProblem =
  pure CoreWhichProblem
traverseCoreF _f _g _h (CoreSyntax stx) =
  pure $ CoreSyntax stx
traverseCoreF _f _g h (CoreCase loc scrut cases) =
  CoreCase loc <$> h scrut <*> for cases \(pat, c) -> (pat,) <$> h c
traverseCoreF _f _g _h (CoreIdentifier n) =
  pure $ CoreIdentifier n
traverseCoreF _f _g _h (CoreSignal s) =
  pure $ CoreSignal s
traverseCoreF _f _g h (CoreIdent ident) =
  CoreIdent <$> traverse h ident
traverseCoreF _f _g h (CoreEmpty args) =
  CoreEmpty <$> traverse h args
traverseCoreF _f _g h (CoreCons args) =
  CoreCons <$> traverse h args
traverseCoreF _f _g h (CoreList args) =
  CoreList <$> traverse h args
traverseCoreF _f _g h (CoreReplaceLoc src dest) =
  CoreReplaceLoc <$> (h src) <*> (h dest)
traverseCoreF f _g h (CoreTypeCase loc scrut cases) =
  CoreTypeCase loc <$> h scrut <*> for cases \(pat, c) -> (,) <$> f pat <*> h c


corePrimitiveCtor :: Text -> [a] -> CoreF typePat pat a
corePrimitiveCtor name args =
  let ctor = Constructor (KernelName kernelName) (ConstructorName name)
  in CoreCtor ctor args

instance (Phased typePat, Phased pat, Phased core) => Phased (CoreF typePat pat core) where
  shift i (CoreIdentifier ident) = CoreIdentifier (shift i ident)
  shift i (CoreSyntax stx) = CoreSyntax (shift i stx)
  shift i other = bimap (shift i) (shift i) other

newtype Core = Core
  { unCore :: CoreF TypePattern ConstructorPattern Core }
  deriving (Eq, Show)
makePrisms ''Core

instance Phased Core where
  shift i (Core c) = Core (shift i c)

instance AlphaEq a => AlphaEq (SyntaxError a) where
  alphaCheck (SyntaxError locations1 message1)
             (SyntaxError locations2 message2) = do
    alphaCheck locations1 locations2
    alphaCheck message1   message2

instance (AlphaEq typePat, AlphaEq pat, AlphaEq core) => AlphaEq (CoreF typePat pat core) where
  alphaCheck (CoreVar var1)
             (CoreVar var2) = do
    alphaCheck var1 var2
  alphaCheck (CoreLam _ var1 body1)
             (CoreLam _ var2 body2) = do
    alphaCheck var1   var2
    alphaCheck body1  body2
  alphaCheck (CoreApp fun1 arg1)
             (CoreApp fun2 arg2) = do
    alphaCheck fun1 fun2
    alphaCheck arg1 arg2
  alphaCheck (CorePure x1)
             (CorePure x2) = do
    alphaCheck x1 x2
  alphaCheck (CoreBind hd1 tl1)
             (CoreBind hd2 tl2) = do
    alphaCheck hd1 hd2
    alphaCheck tl1 tl2
  alphaCheck (CoreSyntaxError syntaxError1)
             (CoreSyntaxError syntaxError2) = do
    alphaCheck syntaxError1 syntaxError2
    alphaCheck syntaxError1 syntaxError2
  alphaCheck (CoreSendSignal signal1)
             (CoreSendSignal signal2) = do
    alphaCheck signal1 signal2
  alphaCheck (CoreWaitSignal signal1)
             (CoreWaitSignal signal2) = do
    alphaCheck signal1 signal2
  alphaCheck (CoreIdentEq how1 e1 g1)
             (CoreIdentEq how2 e2 g2) = do
    guard $ how1 == how2
    alphaCheck e1 e2
    alphaCheck g1 g2
  alphaCheck (CoreSyntax syntax1)
             (CoreSyntax syntax2) = do
    alphaCheck syntax1 syntax2
  alphaCheck (CoreCase _ scrutinee1 cases1)
             (CoreCase _ scrutinee2 cases2) = do
    alphaCheck scrutinee1 scrutinee2
    alphaCheck cases1 cases2
  alphaCheck (CoreIdentifier stx1)
             (CoreIdentifier stx2) = do
    alphaCheck stx1 stx2
  alphaCheck (CoreSignal s1)
             (CoreSignal s2) =
    guard $ s1 == s2
  alphaCheck (CoreIdent scopedIdent1)
             (CoreIdent scopedIdent2) = do
    alphaCheck scopedIdent1 scopedIdent2
  alphaCheck (CoreEmpty scopedEmpty1)
             (CoreEmpty scopedEmpty2) = do
    alphaCheck scopedEmpty1 scopedEmpty2
  alphaCheck (CoreCons scopedCons1)
             (CoreCons scopedCons2) = do
    alphaCheck scopedCons1 scopedCons2
  alphaCheck (CoreList scopedVec1)
             (CoreList scopedVec2) = do
    alphaCheck scopedVec1 scopedVec2
  alphaCheck (CoreCtor ctor1 args1)
             (CoreCtor ctor2 args2) = do
    alphaCheck ctor1 ctor2
    alphaCheck args1 args2
  alphaCheck _ _ = notAlphaEquivalent


instance AlphaEq ConstructorPattern where
  alphaCheck (ConstructorPattern c1 vars1)
             (ConstructorPattern c2 vars2) = do
    alphaCheck c1 c2
    for_ (zip vars1 vars2) (uncurry alphaCheck)
  alphaCheck (AnyConstructor _ x1)
             (AnyConstructor _ x2) = do
    alphaCheck x1 x2
  alphaCheck _ _ = notAlphaEquivalent

instance AlphaEq TypePattern where
  alphaCheck (TypePattern t1)
             (TypePattern t2) =
    alphaCheck t1 t2
  alphaCheck (AnyType _ x1)
             (AnyType _ x2) =
    alphaCheck x1 x2
  alphaCheck _ _ = notAlphaEquivalent

instance AlphaEq Core where
  alphaCheck (Core x1)
             (Core x2) = do
    alphaCheck x1 x2

instance AlphaEq SyntaxPattern where
  alphaCheck (SyntaxPatternIdentifier _ x1)
             (SyntaxPatternIdentifier _ x2) = do
    alphaCheck x1 x2
  alphaCheck SyntaxPatternEmpty
             SyntaxPatternEmpty = do
    pure ()
  alphaCheck (SyntaxPatternCons _ x1 _ xs1)
             (SyntaxPatternCons _ x2 _ xs2) = do
    alphaCheck x1   x2
    alphaCheck xs1  xs2
  alphaCheck (SyntaxPatternList xs1)
             (SyntaxPatternList xs2) = do
    alphaCheck (map snd xs1) (map snd xs2)
  alphaCheck _ _ = notAlphaEquivalent

instance AlphaEq core => AlphaEq (ScopedIdent core) where
  alphaCheck (ScopedIdent ident1 scope1)
             (ScopedIdent ident2 scope2) = do
    alphaCheck ident1 ident2
    alphaCheck scope1 scope2

instance AlphaEq core => AlphaEq (ScopedEmpty core) where
  alphaCheck (ScopedEmpty scope1)
             (ScopedEmpty scope2) = do
    alphaCheck scope1 scope2

instance AlphaEq core => AlphaEq (ScopedCons core) where
  alphaCheck (ScopedCons hd1 tl1 scope1)
             (ScopedCons hd2 tl2 scope2) = do
    alphaCheck hd1    hd2
    alphaCheck tl1    tl2
    alphaCheck scope1 scope2

instance AlphaEq core => AlphaEq (ScopedList core) where
  alphaCheck (ScopedList elements1 scope1)
             (ScopedList elements2 scope2) = do
    alphaCheck elements1 elements2
    alphaCheck scope1    scope2


instance ShortShow a => ShortShow (SyntaxError a) where
  shortShow (SyntaxError locations message)
    = "(SyntaxError "
   ++ shortShow locations
   ++ " "
   ++ shortShow message
   ++ ")"

instance ShortShow Var where
  shortShow (Var x) = shortShow x

instance (ShortShow typePat, ShortShow pat, ShortShow core) =>
         ShortShow (CoreF typePat pat core) where
  shortShow (CoreVar var)
    = "(Var "
   ++ shortShow var
   ++ ")"
  shortShow (CoreLet _ x def body)
    = "(Let "
   ++ shortShow x
   ++ " "
   ++ shortShow def
   ++ " "
   ++ shortShow body
   ++ ")"
  shortShow (CoreLetFun _ f _ x def body)
    = "(LetFun "
   ++ shortShow f
   ++ " "
   ++ shortShow x
   ++ " "
   ++ shortShow def
   ++ " "
   ++ shortShow body
   ++ ")"
  shortShow (CoreLam _ x body)
    = "(Lam "
   ++ shortShow x
   ++ " "
   ++ shortShow body
   ++ ")"
  shortShow (CoreApp fun arg)
    = "(App "
   ++ shortShow fun
   ++ " "
   ++ shortShow arg
   ++ ")"
  shortShow (CoreCtor ctor args)
    = "(Ctor "
   ++ shortShow ctor
   ++ " "
   ++ shortShow args
   ++ ")"
  shortShow (CoreDataCase _ scrut cases)
    = "(DataCase "
   ++ shortShow scrut
   ++ " "
   ++ intercalate ", " (map shortShow cases)
   ++ ")"
  shortShow (CoreError what)
    = "(Error "
   ++ shortShow what
   ++ ")"
  shortShow (CorePure x)
    = "(Pure "
   ++ shortShow x
   ++ ")"
  shortShow (CoreBind hd tl)
    = "(Bind "
   ++ shortShow hd
   ++ " "
   ++ shortShow tl
   ++ ")"
  shortShow (CoreSyntaxError syntaxError)
    = "(SyntaxError "
   ++ shortShow syntaxError
   ++ ")"
  shortShow (CoreSendSignal signal)
    = "(SendSignal "
   ++ shortShow signal
   ++ ")"
  shortShow (CoreWaitSignal signal)
    = "(WaitSignal "
   ++ shortShow signal
   ++ ")"
  shortShow (CoreIdentEq how e1 e2)
    = "(CoreIdentEq " ++ show how
    ++ " " ++ shortShow e1
    ++ " " ++ shortShow e2 ++ ")"
  shortShow (CoreLog msg)
    = "(CoreLog " ++ shortShow msg ++ ")"
  shortShow CoreMakeIntroducer
    = "(CoreMakeIntroducer)"
  shortShow CoreWhichProblem
    = "(CoreWhichProblem)"
  shortShow (CoreSyntax syntax)
    = "(Syntax "
   ++ shortShow syntax
   ++ ")"
  shortShow (CoreCase _ scrutinee cases)
    = "(Case "
   ++ shortShow scrutinee
   ++ " "
   ++ shortShow cases
   ++ ")"
  shortShow (CoreIdentifier stx)
    = "(Identifier "
   ++ shortShow stx
   ++ ")"
  shortShow (CoreSignal signal)
    = shortShow signal
  shortShow (CoreIdent scopedIdent)
    = "(Ident "
   ++ shortShow scopedIdent
   ++ ")"
  shortShow (CoreEmpty scopedEmpty)
    = "(Empty "
   ++ shortShow scopedEmpty
   ++ ")"
  shortShow (CoreCons scopedCons)
    = "(Cons "
   ++ shortShow scopedCons
   ++ ")"
  shortShow (CoreList scopedVec)
    = "(List "
   ++ shortShow scopedVec
   ++ ")"
  shortShow (CoreReplaceLoc loc stx)
    = "(ReplaceLoc "
   ++ shortShow loc ++ " "
   ++ shortShow stx ++ ")"
  shortShow (CoreTypeCase _ scrut pats)
    = "(TypeCase "
   ++ shortShow scrut
   ++ " "
   ++ intercalate ", " (map shortShow pats)
   ++ ")"


instance ShortShow Core where
  shortShow (Core x) = shortShow x

instance ShortShow ConstructorPattern where
  shortShow (ConstructorPattern ctor vars) =
    "(" ++ shortShow ctor ++
    " " ++ intercalate " " (map shortShow vars) ++
    ")"
  shortShow (AnyConstructor ident _var) =
    "(AnyConstructor " ++ shortShow ident ++ " )"

instance ShortShow TypePattern where
  shortShow (TypePattern t) =
    "(" ++ shortShow (fmap fst t) ++ ")"
  shortShow (AnyType ident _var) =
    "(AnyConstructor " ++ shortShow ident ++ " )"


instance ShortShow SyntaxPattern where
  shortShow (SyntaxPatternIdentifier _ x) = shortShow x
  shortShow SyntaxPatternEmpty = "Empty"
  shortShow (SyntaxPatternCons _ x _ xs)
    = "(Cons "
   ++ shortShow x
   ++ " "
   ++ shortShow xs
   ++ ")"
  shortShow (SyntaxPatternList xs)
    = "(List "
   ++ shortShow (map snd xs)
   ++ ")"
  shortShow SyntaxPatternAny = "_"

instance ShortShow core => ShortShow (ScopedIdent core) where
  shortShow (ScopedIdent ident scope)
    = "(ScopedIdent "
   ++ shortShow ident
   ++ " "
   ++ shortShow scope
   ++ ")"

instance ShortShow core => ShortShow (ScopedEmpty core) where
  shortShow (ScopedEmpty scope)
    = "(ScopedEmpty "
   ++ shortShow scope
   ++ ")"

instance ShortShow core => ShortShow (ScopedCons core) where
  shortShow (ScopedCons hd tl scope)
    = "(ScopedCons "
   ++ shortShow hd
   ++ " "
   ++ shortShow tl
   ++ " "
   ++ shortShow scope
   ++ ")"

instance ShortShow core => ShortShow (ScopedList core) where
  shortShow (ScopedList elements scope)
    = "(ScopedList "
   ++ shortShow elements
   ++ " "
   ++ shortShow scope
   ++ ")"
