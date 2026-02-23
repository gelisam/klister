{-|
Module           : Core
Description      : An extensible datatype for expressions

The various instantiations of the openly recursive 'CoreF' datatype represent
expressions in different states of expansion, with the fixpoint 'Core'
representing fully-expanded expressions.
-}

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module Core where

import Control.Lens hiding (elements)
import Control.Monad
import Data.Bifunctor.TH
import Data.Data (Data)
import Data.Foldable
import Data.Text (Text)
import Data.Traversable
import Data.Word
import Data.Int

import Alpha
import Datatype
import ModuleName
import Phase
import Syntax
import Syntax.SrcLoc
import Type
import Unique

import Util.Key

data SyntaxError a = SyntaxError
  { _syntaxErrorLocations :: [a]
  , _syntaxErrorMessage   :: a
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''SyntaxError

newtype Var = Var Unique
  deriving newtype (AlphaEq, Eq, Ord)
  deriving stock Data

instance HasKey Var where
  getKey (Var u) = getKey u
  fromKey i = Var $! fromKey i
  {-# INLINE getKey  #-}
  {-# INLINE fromKey #-}

instance Show Var where
  show (Var i) = "(Var " ++ show (hashUnique i) ++ ")"

newtype MacroVar = MacroVar Unique
  deriving newtype (AlphaEq, Eq, Ord)
  deriving stock Data

instance HasKey MacroVar where
  getKey (MacroVar u) = getKey u
  fromKey i = MacroVar $! fromKey i
  {-# INLINE getKey  #-}
  {-# INLINE fromKey #-}

instance Show MacroVar where
  show (MacroVar i) = "(MacroVar " ++ show (hashUnique i) ++ ")"

data TypePattern
  = TypePattern (TyF (Ident, Var))
  | AnyType Ident Var
  deriving (Data, Eq, Show)

data ConstructorPatternF pat
  = CtorPattern !Constructor [pat]
  | PatternVar Ident Var
  deriving (Data, Eq, Foldable, Functor, Show, Traversable)
makePrisms ''ConstructorPatternF

newtype ConstructorPattern =
  ConstructorPattern { unConstructorPattern :: ConstructorPatternF ConstructorPattern }
  deriving (Data, Eq, Show)
makePrisms ''ConstructorPattern

instance Phased a => Phased (ConstructorPatternF a) where
  shift i = fmap (shift i)

instance Phased ConstructorPattern where
  shift i = over _ConstructorPattern (shift i)

instance Phased TypePattern where
  shift _ = id

data SyntaxPattern
  = SyntaxPatternIdentifier Ident Var
  | SyntaxPatternInteger Ident Var
  | SyntaxPatternInt64 Ident Var
  | SyntaxPatternInt32 Ident Var
  | SyntaxPatternInt16 Ident Var
  | SyntaxPatternInt8  Ident Var
  | SyntaxPatternWord64 Ident Var
  | SyntaxPatternWord32 Ident Var
  | SyntaxPatternWord16 Ident Var
  | SyntaxPatternWord8  Ident Var
  | SyntaxPatternString Ident Var
  | SyntaxPatternEmpty
  | SyntaxPatternCons Ident Var Ident Var
  | SyntaxPatternList [(Ident, Var)]
  | SyntaxPatternAny
  deriving (Data, Eq, Show)
makePrisms ''SyntaxPattern

data ScopedIdent core = ScopedIdent
  { _scopedIdentIdentifier :: core
  , _scopedIdentScope      :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedIdent

data ScopedEmpty core = ScopedEmpty
  { _scopedEmptyScope :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedEmpty

data ScopedCons core = ScopedCons
  { _scopedConsHead  :: core
  , _scopedConsTail  :: core
  , _scopedConsScope :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedCons

data ScopedList core = ScopedList
  { _scopedListElements :: [core]
  , _scopedListScope    :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedList

data ScopedInteger core = ScopedInteger
  { _scopedInteger      :: core
  , _scopedIntegerScope :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedInteger

data ScopedInt64 core = ScopedInt64
  { _scopedInt64      :: core
  , _scopedInt64Scope :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedInt64

data ScopedInt32 core = ScopedInt32
  { _scopedInt32      :: core
  , _scopedInt32Scope :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedInt32

data ScopedInt16 core = ScopedInt16
  { _scopedInt16      :: core
  , _scopedInt16Scope :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedInt16

data ScopedInt8 core = ScopedInt8
  { _scopedInt8      :: core
  , _scopedInt8Scope :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedInt8

data ScopedWord64 core = ScopedWord64
  { _scopedWord64      :: core
  , _scopedWord64Scope :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedWord64

data ScopedWord32 core = ScopedWord32
  { _scopedWord32      :: core
  , _scopedWord32Scope :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedWord32

data ScopedWord16 core = ScopedWord16
  { _scopedWord16      :: core
  , _scopedWord16Scope :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedWord16

data ScopedWord8 core = ScopedWord8
  { _scopedWord8      :: core
  , _scopedWord8Scope :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedWord8


data ScopedString core = ScopedString
  { _scopedString      :: core
  , _scopedStringScope :: core
  }
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
makeLenses ''ScopedString


data HowEq = Free | Bound
  deriving (Data, Eq, Show)

data CoreF typePat pat core
  = CoreVar Var
  | CoreLet Ident Var core core
  | CoreLetFun Ident Var Ident Var core core
  | CoreLam Ident Var core
  | CoreApp core core
  | CoreCtor Constructor [core] -- ^ Constructor application
  | CoreDataCase SrcLoc core [(pat, core)]
  | CoreInteger Integer
  | CoreInt64   Int64
  | CoreInt32   Int32
  | CoreInt16   Int16
  | CoreInt8    Int8
  | CoreWord64  Word64
  | CoreWord32  Word32
  | CoreWord16  Word16
  | CoreWord8   Word8
  | CoreString Text
  | CoreError core
  | CorePureMacro core                  -- :: a -> Macro a
  | CoreBindMacro core core             -- :: Macro a -> (a -> Macro b) -> Macro b
  | CoreSyntaxError (SyntaxError core)  -- :: Macro a
  | CoreIdentEq HowEq core core         -- bound-identifier=? :: Syntax -> Syntax -> Macro Bool
                                        -- free-identifier=?  :: Syntax -> Syntax -> Macro Bool
  | CoreLog core
  | CoreMakeIntroducer
  | CoreWhichProblem
  | CoreSyntax Syntax
  | CoreCase SrcLoc core [(SyntaxPattern, core)]
  | CoreIdent (ScopedIdent core)
  | CoreEmpty (ScopedEmpty core)
  | CoreCons (ScopedCons core)
  | CoreList (ScopedList core)
  | CoreIntegerSyntax (ScopedInteger core)
  | CoreInt64Syntax   (ScopedInt64 core)
  | CoreInt32Syntax   (ScopedInt32 core)
  | CoreInt16Syntax   (ScopedInt16 core)
  | CoreInt8Syntax    (ScopedInt8  core)
  | CoreWord64Syntax  (ScopedWord64 core)
  | CoreWord32Syntax  (ScopedWord32 core)
  | CoreWord16Syntax  (ScopedWord16 core)
  | CoreWord8Syntax   (ScopedWord8  core)
  | CoreStringSyntax  (ScopedString core)
  | CoreReplaceLoc core core
  | CoreTypeCase SrcLoc core [(typePat, core)]
  deriving (Data, Eq, Functor, Foldable, Show, Traversable)
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
mapCoreF _f _g _h (CoreInteger i) =
  CoreInteger i
mapCoreF _f _g _h (CoreWord64 i) =
  CoreWord64 i
mapCoreF _f _g _h (CoreWord32 i) =
  CoreWord32 i
mapCoreF _f _g _h (CoreWord16 i) =
  CoreWord16 i
mapCoreF _f _g _h (CoreWord8 i) =
  CoreWord8 i
mapCoreF _f _g _h (CoreInt64 i) =
  CoreInt64 i
mapCoreF _f _g _h (CoreInt32 i) =
  CoreInt32 i
mapCoreF _f _g _h (CoreInt16 i) =
  CoreInt16 i
mapCoreF _f _g _h (CoreInt8 i) =
  CoreInt8 i
mapCoreF _f _g _h (CoreString str) =
  CoreString str
mapCoreF _f _g h (CoreError msg) =
  CoreError (h msg)
mapCoreF _f _g h (CorePureMacro core) =
  CorePureMacro (h core)
mapCoreF _f _g h (CoreBindMacro act k) =
  CoreBindMacro (h act) (h k)
mapCoreF _f _g h (CoreSyntaxError err) =
  CoreSyntaxError (fmap h err)
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
mapCoreF _f _g h (CoreIdent ident) =
  CoreIdent (fmap h ident)
mapCoreF _f _g h (CoreEmpty args) =
  CoreEmpty (fmap h args)
mapCoreF _f _g h (CoreCons args) =
  CoreCons (fmap h args)
mapCoreF _f _g h (CoreList args) =
  CoreList (fmap h args)
mapCoreF _f _g h (CoreIntegerSyntax str) =
  CoreIntegerSyntax (fmap h str)
mapCoreF _f _g h (CoreWord64Syntax str) =
  CoreWord64Syntax (fmap h str)
mapCoreF _f _g h (CoreWord32Syntax str) =
  CoreWord32Syntax (fmap h str)
mapCoreF _f _g h (CoreWord16Syntax str) =
  CoreWord16Syntax (fmap h str)
mapCoreF _f _g h (CoreWord8Syntax str) =
  CoreWord8Syntax (fmap h str)
mapCoreF _f _g h (CoreInt64Syntax str) =
  CoreInt64Syntax (fmap h str)
mapCoreF _f _g h (CoreInt32Syntax str) =
  CoreInt32Syntax (fmap h str)
mapCoreF _f _g h (CoreInt16Syntax str) =
  CoreInt16Syntax (fmap h str)
mapCoreF _f _g h (CoreInt8Syntax str) =
  CoreInt8Syntax (fmap h str)
mapCoreF _f _g h (CoreStringSyntax str) =
  CoreStringSyntax (fmap h str)
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
traverseCoreF _f _g _h (CoreInteger integer) =
  pure $ CoreInteger integer
traverseCoreF _f _g _h (CoreWord64 wrd) =
  pure $ CoreWord64 wrd
traverseCoreF _f _g _h (CoreWord32 wrd) =
  pure $ CoreWord32 wrd
traverseCoreF _f _g _h (CoreWord16 wrd) =
  pure $ CoreWord16 wrd
traverseCoreF _f _g _h (CoreWord8 wrd) =
  pure $ CoreWord8 wrd
traverseCoreF _f _g _h (CoreInt64 wrd) =
  pure $ CoreInt64 wrd
traverseCoreF _f _g _h (CoreInt32 wrd) =
  pure $ CoreInt32 wrd
traverseCoreF _f _g _h (CoreInt16 wrd) =
  pure $ CoreInt16 wrd
traverseCoreF _f _g _h (CoreInt8 wrd) =
  pure $ CoreInt8 wrd
traverseCoreF _f _g _h (CoreString str) =
  pure $ CoreString str
traverseCoreF _f _g h (CoreError msg) =
  CoreError <$> h msg
traverseCoreF _f _g h (CorePureMacro core) =
  CorePureMacro <$> h core
traverseCoreF _f _g h (CoreBindMacro act k) =
  CoreBindMacro <$> h act <*> h k
traverseCoreF _f _g h (CoreSyntaxError err) =
  CoreSyntaxError <$> traverse h err
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
traverseCoreF _f _g h (CoreIdent ident) =
  CoreIdent <$> traverse h ident
traverseCoreF _f _g h (CoreEmpty args) =
  CoreEmpty <$> traverse h args
traverseCoreF _f _g h (CoreCons args) =
  CoreCons <$> traverse h args
traverseCoreF _f _g h (CoreList args) =
  CoreList <$> traverse h args
traverseCoreF _f _g h (CoreIntegerSyntax arg) =
  CoreIntegerSyntax <$> traverse h arg
traverseCoreF _f _g h (CoreWord64Syntax arg) =
  CoreWord64Syntax <$> traverse h arg
traverseCoreF _f _g h (CoreWord32Syntax arg) =
  CoreWord32Syntax <$> traverse h arg
traverseCoreF _f _g h (CoreWord16Syntax arg) =
  CoreWord16Syntax <$> traverse h arg
traverseCoreF _f _g h (CoreWord8Syntax arg) =
  CoreWord8Syntax <$> traverse h arg
traverseCoreF _f _g h (CoreInt64Syntax arg) =
  CoreInt64Syntax <$> traverse h arg
traverseCoreF _f _g h (CoreInt32Syntax arg) =
  CoreInt32Syntax <$> traverse h arg
traverseCoreF _f _g h (CoreInt16Syntax arg) =
  CoreInt16Syntax <$> traverse h arg
traverseCoreF _f _g h (CoreInt8Syntax arg) =
  CoreInt8Syntax <$> traverse h arg
traverseCoreF _f _g h (CoreStringSyntax arg) =
  CoreStringSyntax <$> traverse h arg
traverseCoreF _f _g h (CoreReplaceLoc src dest) =
  CoreReplaceLoc <$> (h src) <*> (h dest)
traverseCoreF f _g h (CoreTypeCase loc scrut cases) =
  CoreTypeCase loc <$> h scrut <*> for cases \(pat, c) -> (,) <$> f pat <*> h c


corePrimitiveCtor :: Text -> [a] -> CoreF typePat pat a
corePrimitiveCtor name args =
  let ctor = Constructor (KernelName kernelName) (ConstructorName name)
  in CoreCtor ctor args

instance (Phased typePat, Phased pat, Phased core) => Phased (CoreF typePat pat core) where
  shift i (CoreSyntax stx) = CoreSyntax (shift i stx)
  shift i other = bimap (shift i) (shift i) other

-- | A fully-expanded expression, ready to be evaluated.
newtype Core = Core
  { unCore :: CoreF TypePattern ConstructorPattern Core }
  deriving (Data, Eq, Show)
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
  alphaCheck (CorePureMacro x1)
             (CorePureMacro x2) = do
    alphaCheck x1 x2
  alphaCheck (CoreBindMacro hd1 tl1)
             (CoreBindMacro hd2 tl2) = do
    alphaCheck hd1 hd2
    alphaCheck tl1 tl2
  alphaCheck (CoreSyntaxError syntaxError1)
             (CoreSyntaxError syntaxError2) = do
    alphaCheck syntaxError1 syntaxError2
    alphaCheck syntaxError1 syntaxError2
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
  alphaCheck (CoreInteger i1)
             (CoreInteger i2) =
    guard $ i1 == i2
  alphaCheck (CoreWord64 i1)
             (CoreWord64 i2) =
    guard $ i1 == i2
  alphaCheck (CoreWord32 i1)
             (CoreWord32 i2) =
    guard $ i1 == i2
  alphaCheck (CoreWord16 i1)
             (CoreWord16 i2) =
    guard $ i1 == i2
  alphaCheck (CoreWord8 i1)
             (CoreWord8 i2) =
    guard $ i1 == i2
  alphaCheck (CoreInt64 i1)
             (CoreInt64 i2) =
    guard $ i1 == i2
  alphaCheck (CoreInt32 i1)
             (CoreInt32 i2) =
    guard $ i1 == i2
  alphaCheck (CoreInt16 i1)
             (CoreInt16 i2) =
    guard $ i1 == i2
  alphaCheck (CoreInt8 i1)
             (CoreInt8 i2) =
    guard $ i1 == i2
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
  alphaCheck p1 p2 =
    alphaCheck (unConstructorPattern p1) (unConstructorPattern p2)

instance AlphaEq a => AlphaEq (ConstructorPatternF a) where
  alphaCheck (CtorPattern c1 vars1)
             (CtorPattern c2 vars2) = do
    alphaCheck c1 c2
    for_ (zip vars1 vars2) (uncurry alphaCheck)
  alphaCheck (PatternVar _ x1)
             (PatternVar _ x2) = do
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
