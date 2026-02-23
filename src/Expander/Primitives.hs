{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wno-name-shadowing #-}
module Expander.Primitives
  ( -- * Declaration primitives
    define
  , datatype
  , defineMacros
  , example
  , run
  , group
  , meta
  -- * Expression primitives
  , app
  , integerLiteral
  , stringLiteral
  , bindMacro
  , consListSyntax
  , dataCase
  , emptyListSyntax
  , err
  , flet
  , identEqual
  , identSyntax
  , lambda
  , letExpr
  , letSyntax
  , listSyntax
  , integerSyntax
  , int64Syntax
  , int32Syntax
  , int16Syntax
  , int8Syntax
  , word64Syntax
  , word32Syntax
  , word16Syntax
  , word8Syntax
  , stringSyntax
  , makeIntroducer
  , Expander.Primitives.log
  , whichProblem
  , pureMacro
  , quote
  , replaceLoc
  , syntaxCase
  , syntaxError
  , the
  , typeCase
  -- * Pattern primitives
  , elsePattern
  -- * Module primitives
  , makeModule
  -- * Anywhere primitives
  , makeLocalType
  -- * Primitive values
  , unaryIntegerPrim
  , unaryWord64Prim, unaryWord32Prim, unaryWord16Prim, unaryWord8Prim
  , unaryInt64Prim, unaryInt32Prim, unaryInt16Prim, unaryInt8Prim
  , binaryIntegerPrim
  , binaryWord64Prim, binaryWord32Prim, binaryWord16Prim, binaryWord8Prim
  , binaryInt64Prim, binaryInt32Prim, binaryInt16Prim, binaryInt8Prim
  , binaryIntegerPred
  , binaryWord64Pred, binaryWord32Pred, binaryWord16Pred, binaryWord8Pred
  , binaryInt64Pred, binaryInt32Pred, binaryInt16Pred, binaryInt8Pred
  , binaryStringPred
  -- * Helpers
  , prepareVar
  , baseType
  , typeConstructor
  , primitiveDatatype
  ) where

import Control.Lens hiding (List)
import Control.Monad.IO.Class
import Control.Monad
import Control.Monad.Except
import Data.Text (Text)
import qualified Data.Text as T
import Data.Traversable
import Numeric.Natural
import Data.Word
import Data.Int

import Binding
import Core
import Datatype
import qualified Env
import Expander.DeclScope
import Expander.Monad
import Expander.Syntax
import Expander.TC
import Kind
import Module
import ModuleName
import Phase
import Scope
import ScopeSet (ScopeSet)
import qualified ScopeSet
import SplitCore
import SplitType
import Syntax
import Type
import Value

import Debug.Trace

----------------------------
-- Declaration primitives --
----------------------------

type DeclPrim =
  DeclTreePtr -> DeclOutputScopesPtr -> Syntax -> Expand ()

type DeclExpander =
  DeclTreePtr -> ScopeSet -> DeclOutputScopesPtr -> Syntax -> Expand ()

define :: DeclPrim
define dest outScopesDest stx = do
  p <- currentPhase
  Stx _ _ (_, varStx, expr) <- mustHaveEntries stx
  postDefineScope <- freshScope $ T.pack $ "For definition at " ++ show (stxLoc stx)
  x <- addScope' postDefineScope <$> mustBeIdent varStx
  b <- freshBinding
  addDefinedBinding x b
  var <- freshVar
  exprDest <- liftIO $ newSplitCorePtr
  bind b (EIncompleteDefn var x exprDest)
  schPtr <- liftIO $ newSchemePtr
  linkOneDecl dest (Define x var schPtr exprDest)
  t <- inTypeBinder do
    t <- tMetaVar <$> freshMeta (Just KStar)
    forkExpandSyntax (ExprDest t exprDest) expr
    return t
  ph <- currentPhase
  modifyState $ over (expanderDefTypes . at ph . non Env.empty) $
    Env.insert var x schPtr
  forkGeneralizeType exprDest t schPtr
  linkDeclOutputScopes outScopesDest (ScopeSet.singleScopeAtPhase postDefineScope p)

datatype :: DeclPrim
datatype dest outScopesDest stx = do
  Stx scs loc (_ :: Syntax, more) <- mustBeCons stx
  Stx _ _ (nameAndArgs, ctorSpecs) <- mustBeCons (Syntax (Stx scs loc (List more)))
  Stx _ _ (name, args) <- mustBeCons nameAndArgs
  typeArgs <- for (zip [firstSchemeVar..] args) $ \(i, a) ->
    prepareTypeVar i a
  sc <- freshScope $ T.pack $ "For datatype at " ++ show (stxLoc stx)
  let typeScopes = map (view _1) typeArgs ++ [sc]
  realName <- mustBeIdent (addScope' sc name)
  p <- currentPhase
  d <- freshDatatype realName
  let argKinds = map (view _3) typeArgs
  addDatatype realName d argKinds

  ctors <- for ctorSpecs \ spec -> do
    Stx _ _ (cn, ctorArgs) <- mustBeCons spec
    realCN <- mustBeIdent cn
    ctor <- freshConstructor realCN
    let ctorArgs' = [ foldr (addScope p) t typeScopes
                    | t <- ctorArgs
                    ]
    argTypes <- traverse (scheduleType KStar) ctorArgs'
    return (realCN, ctor, argTypes)

  let info =
        DatatypeInfo
        { _datatypeArgKinds = argKinds
        , _datatypeConstructors =
          [ ctor | (_, ctor, _) <- ctors ]
        }
  modifyState $
    set (expanderCurrentDatatypes .
         at p . non mempty .
         at d) $
    Just info

  forkEstablishConstructors (ScopeSet.singleScopeAtPhase sc p) outScopesDest d ctors

  linkOneDecl dest (Data realName (view datatypeName d) argKinds ctors)

defineMacros :: DeclPrim
defineMacros dest outScopesDest stx = do
  Stx _ _ (_, macroList) <- mustHaveEntries stx
  Stx _ _ macroDefs <- mustBeList macroList
  p <- currentPhase
  -- 'sc' allows the newly-defined macros to generate code containing calls to
  -- any of the other newly-defined macros, while 'postDefineScope' allows the
  -- code which follows the @define-macros@ call to refer to the newly-defined
  -- macros.
  sc <- freshScope $ T.pack $ "For macros at " ++ show (stxLoc stx)
  postDefineScope <- freshScope $ T.pack $ "For macro-definition at " ++ show (stxLoc stx)
  macros <- for macroDefs $ \def -> do
    Stx _ _ (mname, mdef) <- mustHaveEntries def
    theName <- addScope' sc <$> mustBeIdent mname
    b <- freshBinding
    addDefinedBinding theName b
    macroDest <- inEarlierPhase $
                   schedule (tFun1 tSyntax (tMacro tSyntax))
                     (addScope p sc mdef)
    v <- freshMacroVar
    bind b $ EIncompleteMacro v theName macroDest
    return (theName, v, macroDest)
  linkOneDecl dest $ DefineMacros macros
  linkDeclOutputScopes outScopesDest ( ScopeSet.insertAtPhase p sc
                                     $ ScopeSet.insertAtPhase p postDefineScope
                                     $ ScopeSet.empty
                                     )

example :: DeclPrim
example dest outScopesDest stx = do
  Stx _ _ (_, expr) <- mustHaveEntries stx
  exprDest <- liftIO $ newSplitCorePtr
  sch <- liftIO newSchemePtr
  linkOneDecl dest (Example (view (unSyntax . stxSrcLoc) stx) sch exprDest)
  t <- inTypeBinder do
    t <- tMetaVar <$> freshMeta (Just KStar)
    forkExpandSyntax (ExprDest t exprDest) expr
    return t
  forkGeneralizeType exprDest t sch
  linkDeclOutputScopes outScopesDest mempty

run :: DeclPrim
run dest outScopesDest stx = do
  Stx _ _ (_, expr) <- mustHaveEntries stx
  exprDest <- liftIO $ newSplitCorePtr
  linkOneDecl dest (Run (stxLoc stx) exprDest)
  forkExpandSyntax (ExprDest (tIO (primitiveDatatype "Unit" [])) exprDest) expr
  linkDeclOutputScopes outScopesDest mempty

meta :: DeclExpander -> DeclPrim
meta expandDeclForms dest outScopesDest stx = do
  (_ :: Syntax, subDecls) <- mustHaveShape stx
  subDest <- newDeclTreePtr
  linkOneDecl dest (Meta subDest)
  inEarlierPhase $
    expandDeclForms subDest mempty outScopesDest =<< addRootScope subDecls

group :: DeclExpander -> DeclPrim
group expandDeclForms dest outScopesDest stx = do
  (_ :: Syntax, decls) <- mustHaveShape stx
  expandDeclForms dest mempty outScopesDest decls

-- Expression primitives
type ExprPrim = Ty -> SplitCorePtr -> Syntax -> Expand ()

err :: ExprPrim
err _t dest stx = do
  Stx _ _ (_, msg) <- mustHaveEntries stx
  msgDest <- schedule tSyntax msg
  linkExpr dest $ CoreError msgDest

the :: ExprPrim
the t dest stx = do
  Stx _ _ (_, ty, expr) <- mustHaveEntries stx
  saveOrigin dest (stxLoc expr)
  tyDest <- scheduleType KStar ty
  -- TODO add type to elaborated program? Or not?
  forkAwaitingType tyDest [TypeThenUnify dest t, TypeThenExpandExpr dest expr]

letExpr :: ExprPrim
letExpr t dest stx = do
  Stx _ _ (_, b, body) <- mustHaveEntries stx
  Stx _ _ (x, def) <- mustHaveEntries b
  (sc, x', coreX) <- prepareVar x
  p <- currentPhase
  psc <- phaseRoot
  (defDest, xTy) <- inTypeBinder do
    xt <- tMetaVar <$> freshMeta (Just KStar)
    defDest <- schedule xt def
    return (defDest, xt)
  sch <- liftIO $ newSchemePtr
  forkGeneralizeType defDest xTy sch
  bodyDest <- withLocalVarType x' coreX sch $
                schedule t $
                addScope p psc $
                addScope p sc body
  linkExpr dest $ CoreLet x' coreX defDest bodyDest

flet :: ExprPrim
flet t dest stx = do
  ft <- inTypeBinder $ tMetaVar <$> freshMeta (Just KStar)
  xt <- inTypeBinder $ tMetaVar <$> freshMeta (Just KStar)
  rt <- inTypeBinder $ tMetaVar <$> freshMeta (Just KStar)
  fsch <- trivialScheme ft
  xsch <- trivialScheme xt
  Stx _ _ (_, b, body) <- mustHaveEntries stx
  Stx _ _ (f, args, def) <- mustHaveEntries b
  Stx _ _ (Identity x) <- mustHaveEntries args
  (fsc, f', coreF) <- prepareVar f
  (xsc, x', coreX) <- prepareVar x
  p <- currentPhase
  psc <- phaseRoot
  defDest <- inTypeBinder $
             withLocalVarType f' coreF fsch $
             withLocalVarType x' coreX xsch $
             schedule rt $
             addScope p psc $
             addScope p xsc $
             addScope p fsc def
  unify dest ft (tFun1 xt rt)
  sch <- liftIO newSchemePtr
  forkGeneralizeType defDest ft sch
  bodyDest <- withLocalVarType f' coreF sch $
              schedule t $
              addScope p psc $
              addScope p fsc body
  linkExpr dest $ CoreLetFun f' coreF x' coreX defDest bodyDest

lambda :: ExprPrim
lambda t dest stx = do
  Stx _ _ (_, arg, body) <- mustHaveEntries stx
  Stx _ _ (Identity theArg) <- mustHaveEntries arg
  (sc, arg', coreArg) <- prepareVar theArg
  p <- currentPhase
  psc <- phaseRoot
  argT <- tMetaVar <$> freshMeta (Just KStar)
  retT <- tMetaVar <$> freshMeta (Just KStar)
  unify dest t (tFun1 argT retT)
  sch <- trivialScheme argT
  bodyDest <-
    withLocalVarType arg' coreArg sch $
      schedule retT $
      addScope p psc $
      addScope p sc body
  linkExpr dest $ CoreLam arg' coreArg bodyDest

app :: ExprPrim
app t dest stx = do
  argT <- tMetaVar <$> freshMeta (Just KStar)
  Stx _ _ (_, fun, arg) <- mustHaveEntries stx
  funDest <- schedule (tFun1 argT t) fun
  argDest <- schedule argT arg
  linkExpr dest $ CoreApp funDest argDest

integerLiteral :: ExprPrim
word64Literal  :: ExprPrim
word32Literal  :: ExprPrim
word16Literal  :: ExprPrim
word8Literal   :: ExprPrim
int64Literal   :: ExprPrim
int32Literal   :: ExprPrim
int16Literal   :: ExprPrim
int8Literal    :: ExprPrim
integerLiteral t dest stx = numLiteral t dest stx mustBeInteger tInteger CoreInteger
word64Literal t dest stx  = numLiteral t dest stx mustBeWord64 tWord64 CoreWord64
word32Literal t dest stx  = numLiteral t dest stx mustBeWord32 tWord32 CoreWord32
word16Literal t dest stx  = numLiteral t dest stx mustBeWord16 tWord16 CoreWord16
word8Literal  t dest stx  = numLiteral t dest stx mustBeWord8  tWord8  CoreWord8
int64Literal t dest stx   = numLiteral t dest stx mustBeInt64 tInt64 CoreInt64
int32Literal t dest stx   = numLiteral t dest stx mustBeInt32 tInt32 CoreInt32
int16Literal t dest stx   = numLiteral t dest stx mustBeInt16 tInt16 CoreInt16
int8Literal  t dest stx   = numLiteral t dest stx mustBeInt8  tInt8  CoreInt8

numLiteral
  :: Ty
  -> SplitCorePtr
  -> Syntax
  -> (Syntax -> Expand (Stx t))
  -> Ty
  -> (t -> CoreF TypePatternPtr PatternPtr SplitCorePtr)
  -> Expand ()
numLiteral t dest stx must_be typ constr = do
  Stx _ _ (_, arg) <- mustHaveEntries stx
  Stx _ _ i <- must_be arg
  unify dest t typ
  linkExpr dest (constr i)
  saveExprType dest t

integerToInt64 :: ExprPrim
integerToInt64 t dest stx = do
  Stx _ _ (_, arg) <- mustHaveEntries stx
  Stx _ _ s <- mustBeInteger arg
  unify dest t tInt64
  linkExpr dest (CoreInt64 $ fromIntegral s)
  saveExprType dest t

stringLiteral :: ExprPrim
stringLiteral t dest stx = do
  Stx _ _ (_, arg) <- mustHaveEntries stx
  Stx _ _ s <- mustBeString arg
  unify dest t tString
  linkExpr dest (CoreString s)
  saveExprType dest t

pureMacro :: ExprPrim
pureMacro t dest stx = do
  Stx _ _ (_, v) <- mustHaveEntries stx
  innerT <- tMetaVar <$> freshMeta (Just KStar)
  unify dest (tMacro innerT) t
  argDest <- schedule innerT v
  linkExpr dest $ CorePureMacro argDest


bindMacro :: ExprPrim
bindMacro t dest stx = do
  a <- tMetaVar <$> freshMeta (Just KStar)
  b <- tMetaVar <$> freshMeta (Just KStar)
  Stx _ _ (_, act, cont) <- mustHaveEntries stx
  actDest <- schedule (tMacro a) act
  contDest <- schedule (tFun1 a (tMacro b)) cont
  unify dest t (tMacro b)
  linkExpr dest $ CoreBindMacro actDest contDest

syntaxError :: ExprPrim
syntaxError t dest stx = do
  a <- tMetaVar <$> freshMeta (Just KStar)
  unify dest t (tMacro a)
  Stx scs srcloc (_, args) <- mustBeCons stx
  Stx _ _ (msg, locs) <- mustBeCons $ Syntax $ Stx scs srcloc (List args)
  msgDest <- schedule tSyntax msg
  locDests <- traverse (schedule tSyntax) locs
  linkExpr dest $ CoreSyntaxError (SyntaxError locDests msgDest)

identEqual :: HowEq -> ExprPrim
identEqual how t dest stx = do
  unify dest t (tMacro (primitiveDatatype "Bool" []))
  Stx _ _ (_, id1, id2) <- mustHaveEntries stx
  newE <- CoreIdentEq how <$> schedule tSyntax id1 <*> schedule tSyntax id2
  linkExpr dest newE

quote :: ExprPrim
quote t dest stx = do
  unify dest t tSyntax
  Stx _ _ (_, quoted) <- mustHaveEntries stx
  linkExpr dest $ CoreSyntax quoted

identSyntax :: ExprPrim
identSyntax t dest stx = do
  unify dest t tSyntax
  Stx _ _ (_, someId, source) <- mustHaveEntries stx
  idDest <- schedule tSyntax someId
  sourceDest <- schedule tSyntax source
  linkExpr dest $ CoreIdent $ ScopedIdent idDest sourceDest

emptyListSyntax :: ExprPrim
emptyListSyntax t dest stx = do
  unify dest t tSyntax
  Stx _ _ (_, source) <- mustHaveEntries stx
  sourceDest <- schedule tSyntax source
  linkExpr dest $ CoreEmpty $ ScopedEmpty sourceDest

consListSyntax :: ExprPrim
consListSyntax t dest stx = do
  unify dest t tSyntax
  Stx _ _ (_, car, cdr, source) <- mustHaveEntries stx
  carDest <- schedule tSyntax car
  cdrDest <- schedule tSyntax cdr
  sourceDest <- schedule tSyntax source
  linkExpr dest $ CoreCons $ ScopedCons carDest cdrDest sourceDest

listSyntax :: ExprPrim
listSyntax t dest stx = do
  unify dest t tSyntax
  Stx _ _ (_, list, source) <- mustHaveEntries stx
  listItems <- mustHaveShape list
  listDests <- traverse (schedule tSyntax) listItems
  sourceDest <- schedule tSyntax source
  linkExpr dest $ CoreList $ ScopedList listDests sourceDest

integerSyntax :: ExprPrim
integerSyntax t dest stx = do
  unify dest t tSyntax
  Stx _ _ (_, int, source) <- mustHaveEntries stx
  intDest <- schedule tInteger int
  sourceDest <- schedule tSyntax source
  linkExpr dest $ CoreIntegerSyntax $ ScopedInteger intDest sourceDest

mkNumSyntax
  :: Ty
  -> SplitCorePtr
  -> Syntax
  -> (SplitCorePtr -> SplitCorePtr -> CoreF TypePatternPtr PatternPtr SplitCorePtr)
  -> Ty
  -> Expand ()
mkNumSyntax t dest stx coreScopeConstr tType = do
  unify dest t tSyntax
  Stx _ _ (_, int, source) <- mustHaveEntries stx
  numDest <- schedule tType int
  sourceDest <- schedule tSyntax source
  linkExpr dest $ coreScopeConstr numDest sourceDest

int64Syntax :: ExprPrim
int32Syntax :: ExprPrim
int16Syntax :: ExprPrim
int8Syntax  :: ExprPrim
int64Syntax t dest stx = mkNumSyntax t dest stx ((CoreInt64Syntax .) . ScopedInt64) tInt64
int32Syntax t dest stx = mkNumSyntax t dest stx ((CoreInt32Syntax .) . ScopedInt32) tInt32
int16Syntax t dest stx = mkNumSyntax t dest stx ((CoreInt16Syntax .) . ScopedInt16) tInt16
int8Syntax t dest stx  = mkNumSyntax t dest stx ((CoreInt8Syntax .) . ScopedInt8) tInt8

word64Syntax :: ExprPrim
word32Syntax :: ExprPrim
word16Syntax :: ExprPrim
word8Syntax  :: ExprPrim
word64Syntax t dest stx = mkNumSyntax t dest stx ((CoreWord64Syntax .) . ScopedWord64) tWord64
word32Syntax t dest stx = mkNumSyntax t dest stx ((CoreWord32Syntax .) . ScopedWord32) tWord32
word16Syntax t dest stx = mkNumSyntax t dest stx ((CoreWord16Syntax .) . ScopedWord16) tWord16
word8Syntax t dest stx  = mkNumSyntax t dest stx ((CoreWord8Syntax .) . ScopedWord8)   tWord8

stringSyntax :: ExprPrim
stringSyntax t dest stx = do
  unify dest t tSyntax
  Stx _ _ (_, str, source) <- mustHaveEntries stx
  strDest <- schedule tString str
  sourceDest <- schedule tSyntax source
  linkExpr dest $ CoreStringSyntax $ ScopedString strDest sourceDest

replaceLoc :: ExprPrim
replaceLoc t dest stx = do
  unify dest t tSyntax
  Stx _ _ (_, loc, valStx) <- mustHaveEntries stx
  locDest <- schedule tSyntax loc
  valStxDest <- schedule tSyntax valStx
  linkExpr dest $ CoreReplaceLoc locDest valStxDest

syntaxCase :: ExprPrim
syntaxCase t dest stx = do
  Stx scs loc (_ :: Syntax, args) <- mustBeCons stx
  Stx _ _ (scrutinee, patterns) <- mustBeCons (Syntax (Stx scs loc (List args)))
  scrutDest <- schedule tSyntax scrutinee
  patternDests <- traverse (mustHaveEntries >=> expandPatternCase t) patterns
  linkExpr dest $ CoreCase loc scrutDest patternDests

letSyntax :: ExprPrim
letSyntax t dest stx = do
  Stx _ loc (_, macro, body) <- mustHaveEntries stx
  Stx _ _ (mName, mdef) <- mustHaveEntries macro
  sc <- freshScope $ T.pack $ "Scope for let-syntax at " ++ show loc
  m <- mustBeIdent mName
  p <- currentPhase
  -- Here, the binding occurrence of the macro gets the
  -- fresh scope at all phases, but later, the scope is only
  -- added to the correct phase in potential use sites.
  -- This prevents the body of the macro (in an earlier
  -- phase) from being able to refer to the macro itself.
  let m' = addScope' sc m
  b <- freshBinding
  addLocalBinding m' b
  v <- freshMacroVar
  macroDest <- inEarlierPhase $ do
    psc <- phaseRoot
    schedule (tFun1 tSyntax (tMacro tSyntax))
      (addScope (prior p) psc mdef)
  forkAwaitingMacro b v m' macroDest (ExprDest t dest) (addScope p sc body)

makeIntroducer :: ExprPrim
makeIntroducer t dest stx = do
  Stx _ _ (Identity mName) <- mustHaveEntries stx
  _ <- mustBeIdent mName
  unify dest theType t
  linkExpr dest $ CoreMakeIntroducer

  where
    theType =
      tMacro (tFun [primitiveDatatype "ScopeAction" [], tSyntax] tSyntax)

log :: ExprPrim
log t dest stx = do
  unify dest (tMacro (primitiveDatatype "Unit" [])) t
  Stx _ _ (_, message) <- mustHaveEntries stx
  msgDest <- schedule tSyntax message
  linkExpr dest $ CoreLog msgDest

whichProblem :: ExprPrim
whichProblem t dest stx = do
  unify dest (tMacro (primitiveDatatype "Problem" [])) t
  Stx _ _ (Identity _) <- mustHaveEntries stx
  linkExpr dest CoreWhichProblem

dataCase :: ExprPrim
dataCase t dest stx = do
  Stx _ loc (_, scrut, cases) <- mustBeConsCons stx
  a <- tMetaVar <$> freshMeta (Just KStar)
  scrutineeDest <- schedule a scrut
  cases' <- traverse (mustHaveEntries >=> scheduleDataPattern t a) cases
  linkExpr dest $ CoreDataCase loc scrutineeDest cases'

typeCase :: ExprPrim
typeCase t dest stx = do
  Stx _ loc (_, scrut, cases) <- mustBeConsCons stx
  a <- tMetaVar <$> freshMeta (Just KStar)
  unify dest (tMacro a) t
  scrutineeDest <- schedule tType scrut
  cases' <- traverse (mustHaveEntries >=> scheduleTypePattern t) cases
  linkExpr dest $ CoreTypeCase loc scrutineeDest cases'

---------------------
-- Type Primitives --
---------------------
type TypePrim =
  (Kind -> SplitTypePtr -> Syntax -> Expand (), TypePatternPtr -> Syntax -> Expand ())

typeConstructor :: TypeConstructor -> [Kind] -> TypePrim
typeConstructor ctor argKinds = (implT, implP)
  where
    implT k dest stx = do
      Stx _ _ (_, args) <- mustBeCons stx
      if length args > length argKinds
        then throwError $ WrongTypeArity stx ctor
                            (fromIntegral $ length argKinds)
                            (length args)
        else do
          let missingArgs :: [Kind]
              missingArgs = drop (length args) argKinds
          equateKinds stx (kFun missingArgs KStar) k
          argDests <- traverse (uncurry scheduleType) (zip argKinds args)
          linkType dest $ TyF ctor argDests
    implP dest stx = do
      Stx _ _ (_, args) <- mustBeCons stx
      if length args > length argKinds
        then throwError $ WrongTypeArity stx ctor
                            (fromIntegral $ length argKinds)
                            (length args)
        else do
          varInfo <- traverse prepareVar args
          sch <- trivialScheme tType
          -- FIXME kind check here
          linkTypePattern dest
            (TypePattern $ TyF ctor [ (varStx, var)
                                    | (_, varStx, var) <- varInfo
                                    ])
            [ (sc, n, x, sch)
            | (sc, n, x) <- varInfo
            ]

baseType :: TypeConstructor -> TypePrim
baseType ctor = typeConstructor ctor []

-------------
-- Modules --
-------------

makeModule :: DeclExpander -> DeclTreePtr -> Syntax -> Expand ()
makeModule expandDeclForms bodyPtr stx =
  view expanderModuleTop <$> getState >>=
  \case
    Just _ ->
      error "TODO throw real error - already expanding a module"
    Nothing -> do
      modifyState $ set expanderModuleTop (Just bodyPtr)
      (_ :: Syntax, body) <- mustHaveShape stx

      outScopesDest <- newDeclOutputScopesPtr
      expandDeclForms bodyPtr mempty outScopesDest body

      pure ()

--------------
-- Anywhere --
--------------

-- | with-unknown-type's implementation: create a named fresh
-- unification variable for macros that only can annotate part of a
-- type.
makeLocalType :: MacroDest -> Syntax -> Expand ()
makeLocalType dest stx = do
  Stx _ _ (_, binder, body) <- mustHaveEntries stx
  Stx _ _ (Identity theVar) <- mustHaveEntries binder
  (sc, n, b) <- varPrepHelper theVar
  meta <- freshMeta Nothing
  let t = TMetaVar meta

  let tyImpl k tdest tstx = do
        k' <- typeVarKind meta
        equateKinds tstx k k'
        _ <- mustBeIdent tstx
        linkType tdest $ TyF t []
  let patImpl _ tstx =
        throwError $ NotValidType tstx

  p <- currentPhase
  addLocalBinding n b
  bind b $ EPrimTypeMacro tyImpl patImpl

  forkExpandSyntax dest (addScope p sc body)

--------------
-- Patterns --
--------------

type PatternPrim = Either (Ty, PatternPtr) TypePatternPtr -> Syntax -> Expand ()

elsePattern :: PatternPrim
elsePattern (Left (scrutTy, dest)) stx = do
  Stx _ _ (_, var) <- mustHaveEntries stx
  ty <- trivialScheme scrutTy
  (sc, x, v) <- prepareVar var
  modifyState $ set (expanderPatternBinders . at dest) $
    Just $ Right (sc, x, v, ty)
  linkPattern dest $ PatternVar x v
elsePattern (Right dest) stx = do
  Stx _ _ (_, var) <- mustHaveEntries stx
  ty <- trivialScheme tType
  (sc, x, v) <- prepareVar var
  linkTypePattern dest
    (AnyType x v)
    [(sc, x, v, ty)]

-------------
-- Helpers --
-------------

-- | Add the primitive macros that expand to datatype invocations
addDatatype :: Ident -> Datatype -> [Kind] -> Expand ()
addDatatype name dt argKinds = do
  name' <- addRootScope' name
  let (tyImpl, patImpl) = typeConstructor (TDatatype dt) argKinds
  let val = EPrimTypeMacro tyImpl patImpl
  b <- freshBinding
  addDefinedBinding name' b
  bind b val


expNum
  :: (Ident -> Var -> a)
  -> Ty
  -> Ty
  -> Syntax
  -> Phase
  -> Syntax
  -> Expand (a, SplitCorePtr)
expNum synPatConstr tType t patVar p rhs = do
  (sc, x', var) <- prepareVar patVar
  let rhs' = addScope p sc rhs
  strSch <- trivialScheme tType
  rhsDest <- withLocalVarType x' var strSch $ schedule t rhs'
  let patOut = synPatConstr x' var
  return (patOut, rhsDest)

expandPatternCase :: Ty -> Stx (Syntax, Syntax) -> Expand (SyntaxPattern, SplitCorePtr)
-- TODO match case keywords hygienically
expandPatternCase t (Stx _ _ (lhs, rhs)) = do
  p <- currentPhase
  sch <- trivialScheme tSyntax
  case lhs of
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "ident")),
                           patVar])) -> do
      (sc, x', var) <- prepareVar patVar
      let rhs' = addScope p sc rhs
      rhsDest <- withLocalVarType x' var sch $ schedule t rhs'
      let patOut = SyntaxPatternIdentifier x' var
      return (patOut, rhsDest)
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "integer")),
                           patVar])) -> expNum SyntaxPatternInteger tInteger t patVar p rhs
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "int64")),
                           patVar])) -> expNum SyntaxPatternInt64 tInt64 t patVar p rhs
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "int32")),
                           patVar])) -> expNum SyntaxPatternInt32 tInt32 t patVar p rhs
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "int16")),
                           patVar])) -> expNum SyntaxPatternInt16 tInt16 t patVar p rhs
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "int8")),
                           patVar])) -> expNum SyntaxPatternInt8  tInt8 t patVar p rhs
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "word64")),
                           patVar])) -> expNum SyntaxPatternWord64 tWord64 t patVar p rhs
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "word32")),
                           patVar])) -> expNum SyntaxPatternWord32 tWord32 t patVar p rhs
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "word16")),
                           patVar])) -> expNum SyntaxPatternWord16 tWord16 t patVar p rhs
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "word8")),
                           patVar])) -> expNum SyntaxPatternWord8  tWord8 t patVar p rhs
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "string")),
                           patVar])) -> do
      (sc, x', var) <- prepareVar patVar
      let rhs' = addScope p sc rhs
      strSch <- trivialScheme tString
      rhsDest <- withLocalVarType x' var strSch $ schedule t rhs'
      let patOut = SyntaxPatternString x' var
      return (patOut, rhsDest)
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "list")),
                           Syntax (Stx _ _ (List vars))])) -> do
      varInfo <- traverse prepareVar vars
      let rhs' = foldr (addScope p) rhs [sc | (sc, _, _) <- varInfo]
      rhsDest <- withLocalVarTypes [(var, vIdent, sch) | (_, vIdent, var) <- varInfo] $
                   schedule t rhs'
      let patOut = SyntaxPatternList [(vIdent, var) | (_, vIdent, var) <- varInfo]
      return (patOut, rhsDest)
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "cons")),
                           car,
                           cdr])) -> do
      (sc, car', carVar) <- prepareVar car
      (sc', cdr', cdrVar) <- prepareVar cdr
      let rhs' = addScope p sc' $ addScope p sc rhs
      rhsDest <- withLocalVarTypes [(carVar, car', sch), (cdrVar, cdr', sch)] $
                   schedule t rhs'
      let patOut = SyntaxPatternCons car' carVar cdr' cdrVar
      return (patOut, rhsDest)
    Syntax (Stx _ _ (List [])) -> do
      rhsDest <- schedule t rhs
      return (SyntaxPatternEmpty, rhsDest)
    Syntax (Stx _ _ (Id "_")) -> do
      rhsDest <- schedule t rhs
      return (SyntaxPatternAny, rhsDest)
    other ->
      throwError $ UnknownPattern other

scheduleDataPattern ::
  Ty -> Ty ->
  Stx (Syntax, Syntax) ->
  Expand (PatternPtr, SplitCorePtr)
scheduleDataPattern exprTy scrutTy (Stx _ _ (patStx, rhsStx@(Syntax (Stx _ loc _)))) = do
  dest <- liftIO newPatternPtr
  forkExpandSyntax (PatternDest scrutTy dest) patStx
  rhsDest <- liftIO newSplitCorePtr
  saveOrigin rhsDest loc
  forkExpanderTask $ AwaitingPattern dest exprTy rhsDest rhsStx
  return (dest, rhsDest)

scheduleTypePattern ::
  Ty -> Stx (Syntax, Syntax) ->
  Expand (TypePatternPtr, SplitCorePtr)
scheduleTypePattern exprTy (Stx _ _ (patStx, rhsStx@(Syntax (Stx _ loc _)))) = do
  dest <- liftIO newTypePatternPtr
  forkExpandSyntax (TypePatternDest dest) patStx
  rhsDest <- liftIO newSplitCorePtr
  saveOrigin rhsDest loc
  forkExpanderTask $ AwaitingTypePattern dest exprTy rhsDest rhsStx
  return (dest, rhsDest)

prepareTypeVar :: SchemeVar -> Syntax -> Expand (Scope, Ident, Kind)
prepareTypeVar i varStx = do
  (sc, α, b) <- varPrepHelper varStx
  k <- KMetaVar <$> liftIO newKindVar
  bind b (ETypeVar k i)
  return (sc, α, k)

varPrepHelper :: Syntax -> Expand (Scope, Ident, Binding)
varPrepHelper varStx = do
  sc <- freshScope $ T.pack $ "For variable " ++ show varStx
  x <- mustBeIdent varStx
  p <- currentPhase
  psc <- phaseRoot
  let x' = addScope' psc $ addScope p sc x
  b <- freshBinding
  addLocalBinding x' b
  return (sc, x', b)


prepareVar :: Syntax -> Expand (Scope, Ident, Var)
prepareVar varStx = do
  (sc, x', b) <- varPrepHelper varStx
  var <- freshVar
  bind b (EVarMacro var)
  return (sc, x', var)

primitiveDatatype :: Text -> [Ty] -> Ty
primitiveDatatype name args =
  let dt = Datatype { _datatypeModule = KernelName kernelName
                    , _datatypeName = DatatypeName name
                    }
  in tDatatype dt args

unaryNumPrim :: (Value -> Value) -> Value
unaryNumPrim = ValueClosure . HO

unaryIntegerPrim :: (Integer -> Integer) -> Value
unaryIntegerPrim f = unaryNumPrim $ \x -> case x of
  (ValueInteger i) -> ValueInteger (f i)
  other -> error (show other)

unaryInt8Prim  :: (Int8 -> Int8)   -> Value
unaryInt16Prim :: (Int16 -> Int16) -> Value
unaryInt32Prim :: (Int32 -> Int32) -> Value
unaryInt64Prim :: (Int64 -> Int64) -> Value
unaryInt8Prim  f = unaryNumPrim $ \(ValueInt8 i)  -> ValueInt8  (f i)
unaryInt16Prim f = unaryNumPrim $ \(ValueInt16 i) -> ValueInt16 (f i)
unaryInt32Prim f = unaryNumPrim $ \(ValueInt32 i) -> ValueInt32 (f i)
unaryInt64Prim f = unaryNumPrim $ \(ValueInt64 i) -> ValueInt64 (f i)

unaryWord8Prim  :: (Word8 -> Word8)   -> Value
unaryWord16Prim :: (Word16 -> Word16) -> Value
unaryWord32Prim :: (Word32 -> Word32) -> Value
unaryWord64Prim :: (Word64 -> Word64) -> Value
unaryWord8Prim  f = unaryNumPrim $ \(ValueWord8 i)  -> ValueWord8  (f i)
unaryWord16Prim f = unaryNumPrim $ \(ValueWord16 i) -> ValueWord16 (f i)
unaryWord32Prim f = unaryNumPrim $ \(ValueWord32 i) -> ValueWord32 (f i)
unaryWord64Prim f = unaryNumPrim $ \(ValueWord64 i) -> ValueWord64 (f i)

binaryIntegerPrim :: (Integer -> Integer -> Integer) -> Value
binaryIntegerPrim f =
  ValueClosure $ HO $ \(ValueInteger i1) ->
    ValueClosure $ HO $ \(ValueInteger i2) -> ValueInteger (f i1 i2)

binaryInt8Prim :: (Int8 -> Int8 -> Int8) -> Value
binaryInt8Prim f =
  ValueClosure $ HO $ \(ValueInt8 i1) ->
    ValueClosure $ HO \(ValueInt8 i2) -> ValueInt8 (f i1 i2)

binaryInt16Prim :: (Int16 -> Int16 -> Int16) -> Value
binaryInt16Prim f =
  ValueClosure $ HO $ \(ValueInt16 i1) ->
    ValueClosure $ HO \(ValueInt16 i2) -> ValueInt16 (f i1 i2)

binaryInt32Prim :: (Int32 -> Int32 -> Int32) -> Value
binaryInt32Prim f =
  ValueClosure $ HO $ \(ValueInt32 i1) ->
    ValueClosure $ HO \(ValueInt32 i2) -> ValueInt32 (f i1 i2)

binaryInt64Prim :: (Int64 -> Int64 -> Int64) -> Value
binaryInt64Prim f =
  ValueClosure $ HO $ \(ValueInt64 i1) ->
    ValueClosure $ HO \(ValueInt64 i2) -> ValueInt64 (f i1 i2)

binaryWord8Prim :: (Word8 -> Word8 -> Word8) -> Value
binaryWord8Prim f =
  ValueClosure $ HO $ \(ValueWord8 i1) ->
    ValueClosure $ HO \(ValueWord8 i2) -> ValueWord8 (f i1 i2)

binaryWord16Prim :: (Word16 -> Word16 -> Word16) -> Value
binaryWord16Prim f =
  ValueClosure $ HO $ \(ValueWord16 i1) ->
    ValueClosure $ HO \(ValueWord16 i2) -> ValueWord16 (f i1 i2)

binaryWord32Prim :: (Word32 -> Word32 -> Word32) -> Value
binaryWord32Prim f =
  ValueClosure $ HO $ \(ValueWord32 i1) ->
    ValueClosure $ HO \(ValueWord32 i2) -> ValueWord32 (f i1 i2)

binaryWord64Prim :: (Word64 -> Word64 -> Word64) -> Value
binaryWord64Prim f =
  ValueClosure $ HO $ \(ValueWord64 i1) ->
    ValueClosure $ HO \(ValueWord64 i2) -> ValueWord64 (f i1 i2)


binaryIntegerPred :: (Integer -> Integer -> Bool) -> Value
binaryIntegerPred f =
  ValueClosure $ HO $ \(ValueInteger i1) ->
    ValueClosure $ HO $ \(ValueInteger i2) ->
      if f i1 i2
        then primitiveCtor "true" []
        else primitiveCtor "false" []

binaryInt8Pred :: (Int8 -> Int8 -> Bool) -> Value
binaryInt8Pred f =
  ValueClosure $ HO $ \(ValueInt8 i1) ->
    ValueClosure $ HO $ \(ValueInt8 i2) ->
      if f i1 i2
        then primitiveCtor "true" []
        else primitiveCtor "false" []

binaryInt16Pred :: (Int16 -> Int16 -> Bool) -> Value
binaryInt16Pred f =
  ValueClosure $ HO $ \(ValueInt16 i1) ->
    ValueClosure $ HO $ \(ValueInt16 i2) ->
      if f i1 i2
        then primitiveCtor "true" []
        else primitiveCtor "false" []

binaryInt32Pred :: (Int32 -> Int32 -> Bool) -> Value
binaryInt32Pred f =
  ValueClosure $ HO $ \(ValueInt32 i1) ->
    ValueClosure $ HO $ \(ValueInt32 i2) ->
      if f i1 i2
        then primitiveCtor "true" []
        else primitiveCtor "false" []

binaryInt64Pred :: (Int64 -> Int64 -> Bool) -> Value
binaryInt64Pred f =
  ValueClosure $ HO $ \(ValueInt64 i1) ->
    ValueClosure $ HO $ \(ValueInt64 i2) ->
      if f i1 i2
        then primitiveCtor "true" []
        else primitiveCtor "false" []

binaryWord8Pred :: (Word8 -> Word8 -> Bool) -> Value
binaryWord8Pred f =
  ValueClosure $ HO $ \(ValueWord8 i1) ->
    ValueClosure $ HO $ \(ValueWord8 i2) ->
      if f i1 i2
        then primitiveCtor "true" []
        else primitiveCtor "false" []

binaryWord16Pred :: (Word16 -> Word16 -> Bool) -> Value
binaryWord16Pred f =
  ValueClosure $ HO $ \(ValueWord16 i1) ->
    ValueClosure $ HO $ \(ValueWord16 i2) ->
      if f i1 i2
        then primitiveCtor "true" []
        else primitiveCtor "false" []

binaryWord32Pred :: (Word32 -> Word32 -> Bool) -> Value
binaryWord32Pred f =
  ValueClosure $ HO $ \(ValueWord32 i1) ->
    ValueClosure $ HO $ \(ValueWord32 i2) ->
      if f i1 i2
        then primitiveCtor "true" []
        else primitiveCtor "false" []

binaryWord64Pred :: (Word64 -> Word64 -> Bool) -> Value
binaryWord64Pred f =
  ValueClosure $ HO $ \(ValueWord64 i1) ->
    ValueClosure $ HO $ \(ValueWord64 i2) ->
      if f i1 i2
        then primitiveCtor "true" []
        else primitiveCtor "false" []


binaryStringPred :: (Text -> Text -> Bool) -> Value
binaryStringPred f =
  ValueClosure $ HO $ \(ValueString str1) ->
    ValueClosure $ HO $ \(ValueString str2) ->
      if f str1 str2
        then primitiveCtor "true" []
        else primitiveCtor "false" []
