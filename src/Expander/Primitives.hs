{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Expander.Primitives
  ( -- * Declaration primitives
    define
  , datatype
  , defineMacros
  , example
  , group
  , meta
  -- * Expression primitives
  , app
  , bindMacro
  , consListSyntax
  , dataCase
  , emptyListSyntax
  , err
  , flet
  , ident
  , identEqual
  , identSyntax
  , lambda
  , letExpr
  , letSyntax
  , listSyntax
  , stringSyntax
  , makeIntroducer
  , Expander.Primitives.log
  , whichProblem
  , oops
  , pureMacro
  , quote
  , replaceLoc
  , sendSignal
  , syntaxCase
  , syntaxError
  , the
  , waitSignal
  , typeCase
  -- * Type primitives
  , arrowType
  , baseType
  , macroType
  , primitiveDatatype
  -- * Pattern primitives
  , elsePattern
  -- * Module primitives
  , makeModule
  -- * Anywhere primitives
  , makeLocalType
  -- * Local primitives
  , prepareVar
  ) where

import Control.Lens hiding (List)
import Control.Monad.IO.Class
import Control.Monad.Except
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as T
import Data.Traversable
import Numeric.Natural

import Binding
import Core
import Datatype
import qualified Env
import Expander.DeclScope
import Expander.Monad
import Expander.Syntax
import Expander.TC
import Module
import ModuleName
import Phase
import Scope
import ScopeSet (ScopeSet)
import qualified ScopeSet
import ShortShow
import SplitCore
import SplitType
import Syntax
import Type

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
  sc <- freshScope $ T.pack $ "For definition at " ++ shortShow (stxLoc stx)
  x <- flip addScope' sc <$> mustBeIdent varStx
  b <- freshBinding
  addDefinedBinding x b
  var <- freshVar
  exprDest <- liftIO $ newSplitCorePtr
  bind b (EIncompleteDefn var x exprDest)
  schPtr <- liftIO $ newSchemePtr
  linkOneDecl dest (Define x var schPtr exprDest)
  t <- inTypeBinder do
    t <- Ty . TMetaVar <$> freshMeta
    forkExpandSyntax (ExprDest t exprDest) expr
    return t
  ph <- currentPhase
  modifyState $ over (expanderDefTypes . at ph . non Env.empty) $
    Env.insert var x schPtr
  forkGeneralizeType exprDest t schPtr
  linkDeclOutputScopes outScopesDest (ScopeSet.singleScopeAtPhase sc p)

datatype :: DeclPrim
datatype dest outScopesDest stx = do
  Stx scs loc (_ :: Syntax, more) <- mustBeCons stx
  Stx _ _ (nameAndArgs, ctorSpecs) <- mustBeCons (Syntax (Stx scs loc (List more)))
  Stx _ _ (name, args) <- mustBeCons nameAndArgs
  typeArgs <- for (zip [0..] args) $ \(i, a) ->
    prepareTypeVar i a
  sc <- freshScope $ T.pack $ "For datatype at " ++ shortShow (stxLoc stx)
  let typeScopes = map fst typeArgs ++ [sc]
  realName <- mustBeIdent (addScope' name sc)
  p <- currentPhase
  let arity = length args
  d <- freshDatatype realName
  addDatatype realName d (fromIntegral arity)

  ctors <- for ctorSpecs \ spec -> do
    Stx _ _ (cn, ctorArgs) <- mustBeCons spec
    realCN <- mustBeIdent cn
    ctor <- freshConstructor realCN
    let ctorArgs' = [ foldr (flip (addScope p)) t typeScopes
                    | t <- ctorArgs
                    ]
    argTypes <- traverse scheduleType ctorArgs'
    return (realCN, ctor, argTypes)

  let info =
        DatatypeInfo
        { _datatypeArity = fromIntegral arity
        , _datatypeConstructors =
          [ ctor | (_, ctor, _) <- ctors ]
        }
  modifyState $
    set (expanderCurrentDatatypes .
         at p . non Map.empty .
         at d) $
    Just info

  forkEstablishConstructors (ScopeSet.singleScopeAtPhase sc p) outScopesDest d ctors

  linkOneDecl dest (Data realName (view datatypeName d) (fromIntegral arity) ctors)

defineMacros :: DeclPrim
defineMacros dest outScopesDest stx = do
  Stx _ _ (_ :: Syntax, macroList) <- mustHaveEntries stx
  Stx _ _ macroDefs <- mustBeList macroList
  p <- currentPhase
  sc <- freshScope $ T.pack $ "For macros at " ++ shortShow (stxLoc stx)
  macros <- for macroDefs $ \def -> do
    Stx _ _ (mname, mdef) <- mustHaveEntries def
    theName <- flip addScope' sc <$> mustBeIdent mname
    b <- freshBinding
    addDefinedBinding theName b
    macroDest <- inEarlierPhase $
                   schedule (Ty (TFun (Ty TSyntax) (Ty (TMacro (Ty TSyntax)))))
                     (addScope p mdef sc)
    v <- freshMacroVar
    bind b $ EIncompleteMacro v theName macroDest
    return (theName, v, macroDest)
  linkOneDecl dest $ DefineMacros macros
  linkDeclOutputScopes outScopesDest (ScopeSet.singleScopeAtPhase sc p)

example :: DeclPrim
example dest outScopesDest stx = do
  Stx _ _ (_ :: Syntax, expr) <- mustHaveEntries stx
  exprDest <- liftIO $ newSplitCorePtr
  sch <- liftIO newSchemePtr
  linkOneDecl dest (Example (view (unSyntax . stxSrcLoc) stx) sch exprDest)
  t <- inTypeBinder do
    t <- Ty . TMetaVar <$> freshMeta
    forkExpandSyntax (ExprDest t exprDest) expr
    return t
  forkGeneralizeType exprDest t sch
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

oops :: ExprPrim
oops _t _dest stx = throwError (InternalError $ "oops" ++ show stx)

err :: ExprPrim
err _t dest stx = do
  Stx _ _ (_ :: Syntax, msg) <- mustHaveEntries stx
  msgDest <- schedule (Ty TSyntax) msg
  linkExpr dest $ CoreError msgDest

the :: ExprPrim
the t dest stx = do
  Stx _ _ (_, ty, expr) <- mustHaveEntries stx
  tyDest <- scheduleType ty
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
    xt <- Ty . TMetaVar <$> freshMeta
    defDest <- schedule xt def
    return (defDest, xt)
  sch <- liftIO $ newSchemePtr
  forkGeneralizeType defDest xTy sch
  bodyDest <- withLocalVarType x' coreX sch $
                schedule t $ addScope p (addScope p body sc) psc
  linkExpr dest $ CoreLet x' coreX defDest bodyDest

flet :: ExprPrim
flet t dest stx = do
  ft <- inTypeBinder $ Ty . TMetaVar <$> freshMeta
  xt <- inTypeBinder $ Ty . TMetaVar <$> freshMeta
  rt <- inTypeBinder $ Ty . TMetaVar <$> freshMeta
  fsch <- trivialScheme ft
  xsch <- trivialScheme xt
  Stx _ _ (_, b, body) <- mustHaveEntries stx
  Stx _ _ (f, args, def) <- mustHaveEntries b
  Stx _ _ x <- mustHaveEntries args
  (fsc, f', coreF) <- prepareVar f
  (xsc, x', coreX) <- prepareVar x
  p <- currentPhase
  psc <- phaseRoot
  defDest <- inTypeBinder $
             withLocalVarType f' coreF fsch $
             withLocalVarType x' coreX xsch $
             schedule rt $
             addScope p (addScope p (addScope p def fsc) xsc) psc
  unify dest ft (Ty (TFun xt rt))
  sch <- liftIO newSchemePtr
  forkGeneralizeType defDest ft sch
  bodyDest <- withLocalVarType f' coreF sch $
              schedule t $
              addScope p (addScope p body fsc) psc
  linkExpr dest $ CoreLetFun f' coreF x' coreX defDest bodyDest

lambda :: ExprPrim
lambda t dest stx = do
  Stx _ _ (_, arg, body) <- mustHaveEntries stx
  Stx _ _ theArg <- mustHaveEntries arg
  (sc, arg', coreArg) <- prepareVar theArg
  p <- currentPhase
  psc <- phaseRoot
  argT <- Ty . TMetaVar <$> freshMeta
  retT <- Ty . TMetaVar <$> freshMeta
  unify dest t (Ty (TFun argT retT))
  sch <- trivialScheme argT
  bodyDest <-
    withLocalVarType arg' coreArg sch $
      schedule retT $ addScope p (addScope p body sc) psc
  linkExpr dest $ CoreLam arg' coreArg bodyDest

app :: ExprPrim
app t dest stx = do
  argT <- Ty . TMetaVar <$> freshMeta
  Stx _ _ (_, fun, arg) <- mustHaveEntries stx
  funDest <- schedule (Ty (TFun argT t)) fun
  argDest <- schedule argT arg
  linkExpr dest $ CoreApp funDest argDest

pureMacro :: ExprPrim
pureMacro t dest stx = do
  Stx _ _ (_ :: Syntax, v) <- mustHaveEntries stx
  innerT <- Ty . TMetaVar <$> freshMeta
  unify dest (Ty (TMacro innerT)) t
  argDest <- schedule innerT v
  linkExpr dest $ CorePure argDest


bindMacro :: ExprPrim
bindMacro t dest stx = do
  a <- Ty . TMetaVar <$> freshMeta
  b <- Ty . TMetaVar <$> freshMeta
  Stx _ _ (_, act, cont) <- mustHaveEntries stx
  actDest <- schedule (Ty (TMacro a)) act
  contDest <- schedule (Ty (TFun a (Ty (TMacro b)))) cont
  unify dest t (Ty (TMacro b))
  linkExpr dest $ CoreBind actDest contDest

syntaxError :: ExprPrim
syntaxError t dest stx = do
  a <- Ty . TMetaVar <$> freshMeta
  unify dest t (Ty (TMacro a))
  Stx scs srcloc (_, args) <- mustBeCons stx
  Stx _ _ (msg, locs) <- mustBeCons $ Syntax $ Stx scs srcloc (List args)
  msgDest <- schedule (Ty TSyntax) msg
  locDests <- traverse (schedule (Ty TSyntax)) locs
  linkExpr dest $ CoreSyntaxError (SyntaxError locDests msgDest)

sendSignal :: ExprPrim
sendSignal t dest stx = do
  unify dest t (Ty (TMacro (primitiveDatatype "Unit" [])))
  Stx _ _ (_ :: Syntax, sig) <- mustHaveEntries stx
  sigDest <- schedule (Ty TSignal) sig
  linkExpr dest $ CoreSendSignal sigDest

waitSignal :: ExprPrim
waitSignal t dest stx = do
  unify dest t (Ty (TMacro (primitiveDatatype "Unit" [])))
  Stx _ _ (_ :: Syntax, sig) <- mustHaveEntries stx
  sigDest <- schedule (Ty TSignal) sig
  linkExpr dest $ CoreWaitSignal sigDest

identEqual :: HowEq -> ExprPrim
identEqual how t dest stx = do
  unify dest t (Ty (TMacro (primitiveDatatype "Bool" [])))
  Stx _ _ (_ :: Syntax, id1, id2) <- mustHaveEntries stx
  newE <- CoreIdentEq how <$> schedule (Ty TSyntax) id1 <*> schedule (Ty TSyntax) id2
  linkExpr dest newE

quote :: ExprPrim
quote t dest stx = do
  unify dest (Ty TSyntax) t
  Stx _ _ (_ :: Syntax, quoted) <- mustHaveEntries stx
  linkExpr dest $ CoreSyntax quoted

ident :: ExprPrim
ident t dest stx = do
  unify dest t (Ty (TSyntax))
  Stx _ _ (_ :: Syntax, someId) <- mustHaveEntries stx
  x@(Stx _ _ _) <- mustBeIdent someId
  linkExpr dest $ CoreIdentifier x

identSyntax :: ExprPrim
identSyntax t dest stx = do
  unify dest t (Ty (TSyntax))
  Stx _ _ (_ :: Syntax, someId, source) <- mustHaveEntries stx
  idDest <- schedule (Ty TSyntax) someId
  sourceDest <- schedule (Ty TSyntax) source
  linkExpr dest $ CoreIdent $ ScopedIdent idDest sourceDest

emptyListSyntax :: ExprPrim
emptyListSyntax t dest stx = do
  unify dest t (Ty (TSyntax))
  Stx _ _ (_ :: Syntax, source) <- mustHaveEntries stx
  sourceDest <- schedule (Ty TSyntax) source
  linkExpr dest $ CoreEmpty $ ScopedEmpty sourceDest

consListSyntax :: ExprPrim
consListSyntax t dest stx = do
  unify dest t (Ty (TSyntax))
  Stx _ _ (_ :: Syntax, car, cdr, source) <- mustHaveEntries stx
  carDest <- schedule (Ty TSyntax) car
  cdrDest <- schedule (Ty TSyntax) cdr
  sourceDest <- schedule (Ty TSyntax) source
  linkExpr dest $ CoreCons $ ScopedCons carDest cdrDest sourceDest

listSyntax :: ExprPrim
listSyntax t dest stx = do
  unify dest t (Ty (TSyntax))
  Stx _ _ (_ :: Syntax, list, source) <- mustHaveEntries stx
  Stx _ _ listItems <- mustHaveEntries list
  listDests <- traverse (schedule (Ty TSyntax)) listItems
  sourceDest <- schedule (Ty TSyntax) source
  linkExpr dest $ CoreList $ ScopedList listDests sourceDest

stringSyntax :: ExprPrim
stringSyntax t dest stx = do
  unify dest t (Ty (TSyntax))
  Stx _ _ (_ :: Syntax, str, source) <- mustHaveEntries stx
  strDest <- schedule (Ty TString) str
  sourceDest <- schedule (Ty TSyntax) source
  linkExpr dest $ CoreStringSyntax $ ScopedString strDest sourceDest

replaceLoc :: ExprPrim
replaceLoc t dest stx = do
  unify dest t (Ty (TSyntax))
  Stx _ _ (_ :: Syntax, loc, valStx) <- mustHaveEntries stx
  locDest <- schedule (Ty TSyntax) loc
  valStxDest <- schedule (Ty TSyntax) valStx
  linkExpr dest $ CoreReplaceLoc locDest valStxDest

syntaxCase :: ExprPrim
syntaxCase t dest stx = do
  Stx scs loc (_ :: Syntax, args) <- mustBeCons stx
  Stx _ _ (scrutinee, patterns) <- mustBeCons (Syntax (Stx scs loc (List args)))
  scrutDest <- schedule (Ty TSyntax) scrutinee
  patternDests <- traverse (mustHaveEntries >=> expandPatternCase t) patterns
  linkExpr dest $ CoreCase loc scrutDest patternDests

letSyntax :: ExprPrim
letSyntax t dest stx = do
  Stx _ loc (_ :: Syntax, macro, body) <- mustHaveEntries stx
  Stx _ _ (mName, mdef) <- mustHaveEntries macro
  sc <- freshScope $ T.pack $ "Scope for let-syntax at " ++ shortShow loc
  m <- mustBeIdent mName
  p <- currentPhase
  -- Here, the binding occurrence of the macro gets the
  -- fresh scope at all phases, but later, the scope is only
  -- added to the correct phase in potential use sites.
  -- This prevents the body of the macro (in an earlier
  -- phase) from being able to refer to the macro itself.
  let m' = addScope' m sc
  b <- freshBinding
  addLocalBinding m' b
  v <- freshMacroVar
  macroDest <- inEarlierPhase $ do
    psc <- phaseRoot
    schedule (Ty (TFun (Ty TSyntax) (Ty (TMacro (Ty TSyntax)))))
      (addScope (prior p) mdef psc)
  forkAwaitingMacro b v m' macroDest (ExprDest t dest) (addScope p body sc)

makeIntroducer :: ExprPrim
makeIntroducer t dest stx = do
  Stx _ _ mName <- mustHaveEntries stx
  _ <- mustBeIdent mName
  unify dest theType t
  linkExpr dest $ CoreMakeIntroducer

  where
    theType =
      Ty $ TMacro $ Ty $ TFun (primitiveDatatype "ScopeAction" []) $
      Ty $ TFun (Ty TSyntax) (Ty TSyntax)

log :: ExprPrim
log t dest stx = do
  unify dest (Ty (TMacro (primitiveDatatype "Unit" []))) t
  Stx _ _ (_ :: Syntax, message) <- mustHaveEntries stx
  msgDest <- schedule (Ty TSyntax) message
  linkExpr dest $ CoreLog msgDest

whichProblem :: ExprPrim
whichProblem t dest stx = do
  unify dest (Ty (TMacro (primitiveDatatype "Problem" []))) t
  Stx _ _ (_ :: Syntax) <- mustHaveEntries stx
  linkExpr dest CoreWhichProblem

dataCase :: ExprPrim
dataCase t dest stx = do
  Stx _ loc (_, scrut, cases) <- mustBeConsCons stx
  a <- Ty . TMetaVar <$> freshMeta
  scrutineeDest <- schedule a scrut
  cases' <- traverse (mustHaveEntries >=> scheduleDataPattern t a) cases
  linkExpr dest $ CoreDataCase loc scrutineeDest cases'

typeCase :: ExprPrim
typeCase t dest stx = do
  Stx _ loc (_, scrut, cases) <- mustBeConsCons stx
  a <- Ty . TMetaVar <$> freshMeta
  unify dest (Ty (TMacro a)) t
  scrutineeDest <- schedule (Ty TType) scrut
  cases' <- traverse (mustHaveEntries >=> scheduleTypePattern t) cases
  linkExpr dest $ CoreTypeCase loc scrutineeDest cases'

---------------------
-- Type Primitives --
---------------------
type TypePrim =
  (SplitTypePtr -> Syntax -> Expand (), TypePatternPtr -> Syntax -> Expand ())

baseType :: (forall a . TyF a) -> TypePrim
baseType ctor = (implT, implP)
  where
    implT dest stx = do
      _actualName <- mustBeIdent stx
      linkType dest ctor
    implP dest stx = do
      _actualName <- mustBeIdent stx
      linkTypePattern dest $ TypePattern ctor

arrowType :: TypePrim
arrowType = (implT, implP)
  where
    implT dest stx = do
      Stx _ _ (_ :: Syntax, arg, ret) <- mustHaveEntries stx
      argDest <- scheduleType arg
      retDest <- scheduleType ret
      linkType dest (TFun argDest retDest)
    implP dest stx = do
      Stx _ _ (_ :: Syntax, arg, ret) <- mustHaveEntries stx
      (sc1, n1, x1) <- prepareVar arg
      (sc2, n2, x2) <- prepareVar ret
      sch <- trivialScheme $ Ty $ TType
      modifyState $
        set (expanderPatternBinders . at (Right dest)) $
        Just [(sc1, n1, x1, sch), (sc2, n2, x2, sch)]
      linkTypePattern dest $ TypePattern $ TFun (n1, x1) (n2, x2)

macroType :: TypePrim
macroType = unaryType TMacro

unaryType :: (forall a . a -> TyF a) -> TypePrim
unaryType ctor = (implT, implP)
  where
    implT dest stx = do
      Stx _ _ (_ :: Syntax, t) <- mustHaveEntries stx
      tDest <- scheduleType t
      linkType dest (ctor tDest)
    implP dest stx = do
      Stx _ _ (_ :: Syntax, a) <- mustHaveEntries stx
      (sc, n, x) <- prepareVar a
      sch <- trivialScheme $ Ty $ TType
      modifyState $
        set (expanderPatternBinders . at (Right dest)) $
        Just [(sc, n, x, sch)]
      linkTypePattern dest $ TypePattern $ ctor (n, x)

-------------
-- Modules --
-------------

makeModule :: DeclExpander -> Syntax -> Expand ()
makeModule expandDeclForms stx =
  view expanderModuleTop <$> getState >>=
  \case
    Just _ ->
      error "TODO throw real error - already expanding a module"
    Nothing -> do
      bodyPtr <- newDeclTreePtr
      modifyState $ set expanderModuleTop (Just bodyPtr)
      Stx _ _ (_ :: Syntax, name, body) <- mustHaveEntries stx
      _actualName <- mustBeIdent name

      outScopesDest <- newDeclOutputScopesPtr
      expandDeclForms bodyPtr mempty outScopesDest body

      pure ()

--------------
-- Anywhere --
--------------

makeLocalType :: MacroDest -> Syntax -> Expand ()
makeLocalType dest stx = do
  Stx _ _ (_ :: Syntax, binder, body) <- mustHaveEntries stx
  Stx _ _ theVar <- mustHaveEntries binder
  (sc, n, b) <- varPrepHelper theVar
  t <- TMetaVar <$> freshMeta

  let tyImpl tdest tstx = do
        _ <- mustBeIdent tstx
        linkType tdest t
  let patImpl _ tstx =
        throwError $ NotValidType tstx

  p <- currentPhase
  addLocalBinding n b
  bind b $ EPrimTypeMacro tyImpl patImpl

  forkExpandSyntax dest (addScope p body sc)

--------------
-- Patterns --
--------------

type PatternPrim = Either (Ty, Ty, PatternPtr) (Ty, TypePatternPtr) -> Syntax -> Expand ()

elsePattern :: PatternPrim
elsePattern (Left (_exprTy, scrutTy, dest)) stx = do
  Stx _ _ (_ :: Syntax, var) <- mustHaveEntries stx
  ty <- trivialScheme scrutTy
  (sc, x, v) <- prepareVar var
  modifyState $ set (expanderPatternBinders . at (Left dest)) $
    Just [(sc, x, v, ty)]
  linkPattern dest $ AnyConstructor x v
elsePattern (Right (_exprTy, dest)) stx = do
  Stx _ _ (_ :: Syntax, var) <- mustHaveEntries stx
  ty <- trivialScheme (Ty TType)
  (sc, x, v) <- prepareVar var
  modifyState $ set (expanderPatternBinders . at (Right dest)) $
    Just [(sc, x, v, ty)]
  linkTypePattern dest $ AnyType x v

-------------
-- Helpers --
-------------

addDatatype :: Ident -> Datatype -> Natural -> Expand ()
addDatatype name dt arity = do
  name' <- addRootScope' name
  let implType =
        \dest stx -> do
          Stx _ _ (me, args) <- mustBeCons stx
          _ <- mustBeIdent me
          if length args /= fromIntegral arity
            then throwError $ WrongDatatypeArity stx dt arity (length args)
            else do
              argDests <- traverse scheduleType args
              linkType dest $ TDatatype dt argDests
      implPat =
        \dest stx -> do
          Stx _ _ (me, args) <- mustBeCons stx
          _ <- mustBeIdent me
          if length args /= fromIntegral arity
            then throwError $ WrongDatatypeArity stx dt arity (length args)
            else do
              patVarInfo <- traverse prepareVar args
              sch <- trivialScheme $ Ty $ TType
              modifyState $
                set (expanderPatternBinders . at (Right dest)) $
                Just [ (sc, n, x, sch)
                     | (sc, n, x) <- patVarInfo
                     ]
              linkTypePattern dest $ TypePattern $ TDatatype dt [(n, x) | (_, n, x) <- patVarInfo]
  let val = EPrimTypeMacro implType implPat
  b <- freshBinding
  addDefinedBinding name' b
  bind b val


expandPatternCase :: Ty -> Stx (Syntax, Syntax) -> Expand (SyntaxPattern, SplitCorePtr)
-- TODO match case keywords hygienically
expandPatternCase t (Stx _ _ (lhs, rhs)) = do
  p <- currentPhase
  sch <- trivialScheme (Ty TSyntax)
  case lhs of
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "ident")),
                           patVar])) -> do
      (sc, x', var) <- prepareVar patVar
      let rhs' = addScope p rhs sc
      rhsDest <- withLocalVarType x' var sch $ schedule t rhs'
      let patOut = SyntaxPatternIdentifier x' var
      return (patOut, rhsDest)
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "string")),
                           patVar])) -> do
      (sc, x', var) <- prepareVar patVar
      let rhs' = addScope p rhs sc
      strSch <- trivialScheme (Ty TString)
      rhsDest <- withLocalVarType x' var strSch $ schedule t rhs'
      let patOut = SyntaxPatternString x' var
      return (patOut, rhsDest)
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "list")),
                           Syntax (Stx _ _ (List vars))])) -> do
      varInfo <- traverse prepareVar vars
      let rhs' = foldr (flip (addScope p)) rhs [sc | (sc, _, _) <- varInfo]
      rhsDest <- withLocalVarTypes [(var, vIdent, sch) | (_, vIdent, var) <- varInfo] $
                   schedule t rhs'
      let patOut = SyntaxPatternList [(vIdent, var) | (_, vIdent, var) <- varInfo]
      return (patOut, rhsDest)
    Syntax (Stx _ _ (List [Syntax (Stx _ _ (Id "cons")),
                           car,
                           cdr])) -> do
      (sc, car', carVar) <- prepareVar car
      (sc', cdr', cdrVar) <- prepareVar cdr
      let rhs' = addScope p (addScope p rhs sc) sc'
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
  forkExpandSyntax (PatternDest exprTy scrutTy dest) patStx
  rhsDest <- liftIO newSplitCorePtr
  saveOrigin rhsDest loc
  forkExpanderTask $ AwaitingPattern (Left dest) exprTy rhsDest rhsStx
  return (dest, rhsDest)

scheduleTypePattern ::
  Ty -> Stx (Syntax, Syntax) ->
  Expand (TypePatternPtr, SplitCorePtr)
scheduleTypePattern exprTy (Stx _ _ (patStx, rhsStx@(Syntax (Stx _ loc _)))) = do
  dest <- liftIO newTypePatternPtr
  forkExpandSyntax (TypePatternDest exprTy dest) patStx
  rhsDest <- liftIO newSplitCorePtr
  saveOrigin rhsDest loc
  forkExpanderTask $ AwaitingPattern (Right dest) exprTy rhsDest rhsStx
  return (dest, rhsDest)

prepareTypeVar :: Natural -> Syntax -> Expand (Scope, Ident)
prepareTypeVar i varStx = do
  (sc, α, b) <- varPrepHelper varStx
  bind b (ETypeVar i)
  return (sc, α)

varPrepHelper :: Syntax -> Expand (Scope, Ident, Binding)
varPrepHelper varStx = do
  sc <- freshScope $ T.pack $ "For variable " ++ shortShow varStx
  x <- mustBeIdent varStx
  p <- currentPhase
  psc <- phaseRoot
  let x' = addScope' (addScope p x sc) psc
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
  in Ty $ TDatatype dt args

