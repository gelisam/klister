{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

{- Note [The CEK interpreter]:

The Klister interpreter is a straightforward implementation of a CEK
interpreter. The interpreter keeps three kinds of state:

-- C: Control      ::= The thing that is being evaluated
-- E: Environment  ::= The interpreter environment
-- K: Kontinuation ::= The syntactic context of the thing that is being interpreted

Why a CEK? A CEK interpreter allows us to have precise control over the
evaluation of a klister program. For example, because the interpreter keeps a
reference to the kontinuation we can provide stack traces. This handle also
makes a more advanced debugger possible. Upon an evaluation error we could save
the kontinuation stack, over write a variable in the environment a la common
lisp or even rewind the evaluation

The bird's eye view:

-}

module Evaluator
  ( EvalError (..)
  , EvalResult (..)
  , TypeError (..)
  , evaluate
  , evaluateIn
  , evaluateWithExtendedEnv
  , evalErrorType
  , applyInEnv
  , apply
  , doTypeCase
  , try
  ) where

import Control.Lens hiding (List, elements)
import Control.Exception hiding (TypeError, evaluate)
import Data.Data (Typeable)
import Data.Text (Text)
import Data.List (foldl')
import qualified Data.Text as T

import Datatype
import Core
import Env
import ShortShow
import Syntax
import Syntax.SrcLoc
import Type
import Value

-- -----------------------------------------------------------------------------
-- Interpreter Data Types


data EvalResult
  = ExampleResult SrcLoc VEnv Core (Scheme Ty) Value
  | IOResult (IO ())

-- TODO: more precise representation
type Type = Text

data TypeError = TypeError
  { _typeErrorExpected :: Type
  , _typeErrorActual   :: Type
  }
  deriving (Eq, Show)
makeLenses ''TypeError

data EvalError
  = EvalErrorUnbound Var
  | EvalErrorType TypeError
  | EvalErrorCase SrcLoc Value
  | EvalErrorUser Syntax
  deriving (Show, Typeable)
makePrisms ''EvalError
instance Exception EvalError

-- | The Kontinuation type. The naming convention InFoo means that the subject
-- of evaluation in the CEK machine is Foo. For example, when the continuation
-- is 'InArg' the subject of evaluation is the argument of the function and the
-- continuation holds the un-evaluated function symbol in its first field.
data Kont where

  Halt :: Kont
  -- ^ Marks the evaluator finishing

  -- functions
  InArg :: !(CoreF TypePattern ConstructorPattern Core) -> !VEnv -> !Kont -> Kont
  -- ^ The argument is being evaluated, so hold onto the function symbol.
  InFun :: !Value -> !VEnv -> !Kont -> Kont
  -- ^ The function is being evaluated, so hold onto the evaluated argument.

  InLetDef :: !Ident -> !Var -> !(CoreF TypePattern ConstructorPattern Core) -> !VEnv -> !Kont -> Kont
  -- ^ Evaluating the let def

  -- constructors
  InCtor :: !Constructor -> ![CoreF TypePattern ConstructorPattern Core] -> ![Value] -> !VEnv -> !Kont -> Kont

  -- Cases
  InCaseScrut     :: ![(SyntaxPattern, Core)] -> !SrcLoc -> !VEnv -> !Kont -> Kont
  InDataCaseScrut :: ![(ConstructorPattern, Core)] -> !SrcLoc -> !VEnv -> !Kont -> Kont
  InTypeCaseScrut :: ![(TypePattern, Core)] -> !SrcLoc -> !VEnv -> !Kont -> Kont

  -- lists
  InConsHd :: !Core -> !(CoreF TypePattern ConstructorPattern Core) -> !VEnv -> !Kont -> Kont
  InConsTl :: !Core -> !Syntax -> !VEnv -> !Kont -> Kont
  InList   :: !Core -> ![Core] -> ![Syntax] -> !VEnv -> !Kont -> Kont

  -- idents
  InIdent :: !Core -> !VEnv -> !Kont -> Kont
  InIdentEqL :: !HowEq -> !Core -> !VEnv -> !Kont -> Kont
  InIdentEqR :: !HowEq -> !Value -> !VEnv -> !Kont -> Kont

  -- Macros
  InPureMacro :: !VEnv -> !Kont -> Kont
  InBindMacroHd :: !Core -> !VEnv -> !Kont -> Kont
  InBindMacroTl :: !MacroAction -> !VEnv -> !Kont -> Kont

  -- atomics
  InInteger :: !Core -> !VEnv -> !Kont -> Kont
  InString  :: !Core -> !VEnv -> !Kont -> Kont
  InLoc     :: !Core -> !VEnv -> !Kont -> Kont
  InLocStx  :: !SrcLoc -> !VEnv -> !Kont -> Kont

  -- scope
  InScope :: !(ExprF Syntax) -> !VEnv -> !Kont -> Kont

  -- logs and errors
  InLog   :: !VEnv -> !Kont -> Kont
  InError :: !VEnv -> !Kont -> Kont

  InSyntaxErrorMessage   :: ![Core] -> !VEnv -> !Kont -> Kont
  InSyntaxErrorLocations :: !Syntax -> ![Core] -> ![Syntax] -> !VEnv -> !Kont -> Kont

-- | The state of the evaluator
data EState where
  Down :: !(CoreF TypePattern ConstructorPattern Core) -> !VEnv -> !Kont -> EState
  -- ^ 'Down', we are searching the AST for a redux and building up the stack of
  -- continuations
  Up   :: !Value -> !VEnv -> !Kont -> EState
  -- ^ 'Up', means we have performed some evaluation on a redex and are
  -- returning a value up the stack


-- -----------------------------------------------------------------------------
-- The evaluator. The CEK machine is a state machine, the @step@ function moves
-- the state machine a single step of evaluation. This is the heart of the
-- evaluator.


-- | Make a single step transition in the CEK state machine.
step :: EState -> EState
step done@(Up _val _ Halt) = done
-- Upsweep, returning a value after evaluating a redex
step (Up v e k) =
  case k of
    -- functions
    -- we evaluated the arg to get a closed so now we evaluate the fun
    (InArg c env kont) -> Down c env (InFun v e kont)
    -- we evaluated the fun so now do the application
    (InFun val env kont) -> apply' env (evalAsClosure v) val kont


    --
    -- we have the value for the def, now eval the body
    (InLetDef id' var body env kont) -> Down body (extend id' var v env) kont

    -- done, this could be a hack
    (InCtor c [] v_args _env kont) -> Up (ValueCtor c (reverse $ v : v_args)) e kont
    -- still processing
    (InCtor c (a:as) vs env kont) -> Down a env (InCtor c as (v:vs) env kont)

    -- Cases
    (InCaseScrut cs loc env kont)     -> doCase loc v cs env kont
    (InDataCaseScrut cs loc env kont) -> doDataCase loc v cs env kont
    (InTypeCaseScrut cs loc env kont) ->
      Up (ValueMacroAction $ MacroActionTypeCase e loc (evalAsType v) cs) env kont

    -- Syntax
    (InIdent scope env kont) -> case v of
      ValueSyntax stx ->
        case _unSyntax stx of
          (Stx _ _ expr) -> case expr of
            Integer _ ->
              error $ show $ EvalErrorType $ TypeError
                                { _typeErrorExpected = "id"
                                , _typeErrorActual   = "integer"
                                }
            String _ ->
              error $ show $ EvalErrorType $ TypeError
                                { _typeErrorExpected = "id"
                                , _typeErrorActual   = "string"
                                }
            List _ ->
              error $ show $ EvalErrorType $ TypeError
                                { _typeErrorExpected = "id"
                                , _typeErrorActual   = "list"
                                }
            name@(Id _) -> Down (unCore scope) env (InScope name env kont)
      other -> error $ "In Ident " ++ show other
    (InIdentEqL how r env kont)  -> Down (unCore r) env (InIdentEqR how v env kont)
    (InIdentEqR how lv env kont) -> Up (ValueMacroAction $ MacroActionIdentEq how lv v) env kont

    -- Short circuit to speed this up, we could issue an Down and do this recursively
    (InScope expr env kont) -> case evalAsSyntax v of
        Syntax (Stx scopeSet loc _) -> Up (ValueSyntax $ Syntax $ Stx scopeSet loc expr) env kont

    -- lists
    (InConsHd scope tl env kont) -> Down tl env (InConsTl scope (evalAsSyntax v) env kont)
    (InConsTl scope hd env kont) -> case evalAsSyntax v of
        Syntax (Stx _ _ expr) ->
          case expr of
            List tl -> Down (unCore scope) env (InScope (List $ hd : tl) env kont)
            String _ ->
              error $ show $ EvalErrorType $ TypeError
              { _typeErrorExpected = "list"
              , _typeErrorActual   = "string"
              }
            Id _ -> error $ show $ EvalErrorType $ TypeError
              { _typeErrorExpected = "list"
              , _typeErrorActual   = "id"
              }
            Integer _ ->
              error $ show $ EvalErrorType $ TypeError
              { _typeErrorExpected = "list"
              , _typeErrorActual   = "integer"
              }

    -- done
    (InList scope [] dones env kont) ->
      Down (unCore scope) e (InScope (List $ reverse $ evalAsSyntax v : dones) env kont)
    -- still some todo
    (InList scope (el:els) dones env kont) -> 
      Down (unCore el) env (InList scope els (evalAsSyntax v : dones) env kont)

    -- Macros
    (InPureMacro env kont) -> Up (ValueMacroAction $ MacroActionPure v) env kont
    (InBindMacroHd tl env kont) ->
      Down (unCore tl) env (InBindMacroTl (evalAsMacroAction v) env kont)
    (InBindMacroTl macroAction env kont) ->
      Up (ValueMacroAction $ MacroActionBind macroAction (evalAsClosure v)) env kont

    -- Syntax and Atomics
    (InInteger scope env kont) ->
      Down (unCore scope) env (InScope (Integer $ evalAsInteger v) env kont)
    (InString scope env kont) ->
      Down (unCore scope) env (InScope (String $ evalAsString v) env kont)
    (InLoc stx env kont) -> case evalAsSyntax v of
      Syntax (Stx _ newLoc _) -> Down (unCore stx) env (InLocStx newLoc env kont)
    (InLocStx loc env kont) -> case evalAsSyntax v of
      Syntax (Stx scs _ contents) -> Up (ValueSyntax $ Syntax $ Stx scs loc contents) env kont
    (InLog   env kont)   -> Up (ValueMacroAction (MacroActionLog $ evalAsSyntax v)) env kont

    -- Errors and TODO: a debugger hook
    (InError _env _kont) -> error $ show v
    (InSyntaxErrorMessage locs env kont) ->
      let msg_syn = evalAsSyntax v
      in case locs of
        -- done
        []     -> Up (ValueMacroAction $ MacroActionSyntaxError
                          (SyntaxError { _syntaxErrorMessage   = msg_syn
                                       , _syntaxErrorLocations = mempty
                                       })) env kont

        (l:ls) -> Down (unCore l) env (InSyntaxErrorLocations msg_syn ls mempty env kont)

      -- done
    (InSyntaxErrorLocations msg_syn [] dones env kont) ->
        Up (ValueMacroAction
                $ MacroActionSyntaxError (SyntaxError { _syntaxErrorMessage   = msg_syn
                                                      , _syntaxErrorLocations = dones
                                                      })) env kont
    (InSyntaxErrorLocations msg (l:ls) dones env kont) ->
      Down (unCore l) env (InSyntaxErrorLocations msg ls (evalAsSyntax v : dones) env kont)

-- the downsweep, searching for a redex to evaluate.
step (Down c env k)  =
  case c of

    -- atoms
    (CoreString s)    -> Up (ValueString s) env k
    (CoreInteger i)   -> Up (ValueInteger i) env k
    (CoreIntegerSyntax (ScopedInteger int scope)) -> Down (unCore int) env (InInteger scope env k)
    (CoreStringSyntax  (ScopedString  str scope)) -> Down (unCore str) env (InString scope env k)
    (CoreSyntax s)    -> Up (ValueSyntax s) env k
    (CoreError what)  -> Down (unCore what) env (InError env k)
    (CoreEmpty (ScopedEmpty scope)) -> Down (unCore scope) env (InScope (List mempty) env k)
    CoreMakeIntroducer -> Up (ValueMacroAction MacroActionIntroducer)   env k
    CoreWhichProblem   -> Up (ValueMacroAction MacroActionWhichProblem) env k


    -- variables and binders
    (CoreVar var) ->
      case lookupVal var env of
        Just val -> Up val env k
        _        -> error $ show $ EvalErrorUnbound var

    (CoreLet ident var def body) ->
      Down (unCore def) env (InLetDef ident var (unCore body) env k)

    (CoreLetFun fIdent fVar argIdent argVar def body) ->
      let vFun = ValueClosure $ FO $ FOClosure
            { _closureEnv   = Env.insert fVar fIdent vFun env
            , _closureIdent = argIdent
            , _closureVar   = argVar
            , _closureBody  = def
            }
          newEnv = Env.insert fVar fIdent vFun env
      in Down (unCore body) newEnv k

    (CoreCtor con args) -> case args of
                           -- just a symbol, shortcut out
                           []     -> Up (ValueCtor con mempty) env k
                           -- process fields left to right
                           (f:fs) -> Down (unCore f) env (InCtor con (fmap unCore fs) mempty env k)


    -- lambdas and application
    (CoreLam ident var body) ->
      let lam = ValueClosure $ FO $ FOClosure
            { _closureEnv   = env
            , _closureIdent = ident
            , _closureVar   = var
            , _closureBody  = body
            }
      in Up lam env k
    (CoreApp fun arg) -> Down (unCore arg) env (InArg (unCore fun) env k)


    -- cases
    (CoreCase     loc scrutinee cases) -> Down (unCore scrutinee) env (InCaseScrut     cases loc env k)
    (CoreDataCase loc scrutinee cases) -> Down (unCore scrutinee) env (InDataCaseScrut cases loc env k)
    (CoreTypeCase loc scrut cases)     -> Down (unCore scrut)     env (InTypeCaseScrut cases loc env k)

    (CoreIdent (ScopedIdent ident scope)) -> Down (unCore ident) env (InIdent scope env k)
    (CoreIdentEq how l r)                 -> Down (unCore l)     env (InIdentEqL how r env k)

    (CoreCons (ScopedCons hd tl scope))   -> Down (unCore hd) env (InConsHd scope (unCore tl) env k)
    -- empty, short circuit
    (CoreList (ScopedList ls scope)) -> case ls of
                                         []     -> Down (unCore scope) env (InScope (List []) env k)
                                         (e:es) -> Down (unCore e) env (InList scope es mempty env k)

    (CoreReplaceLoc loc stx) -> Down (unCore loc) env (InLoc stx env k)

    -- macros
    (CorePureMacro arg)   -> Down (unCore arg) env (InPureMacro env k)
    (CoreBindMacro hd tl) -> Down (unCore hd) env (InBindMacroHd tl env k)
    -- others
    (CoreLog msg)      -> Down (unCore msg) env (InLog env k)
    (CoreSyntaxError err) ->
      Down (unCore $ _syntaxErrorMessage err) env (InSyntaxErrorMessage (_syntaxErrorLocations err) env k)


-- -----------------------------------------------------------------------------
-- Helper Functions


evalAsClosure :: Value -> Closure
evalAsClosure = \case
    ValueClosure closure -> closure
    other                -> error $ show $ evalErrorType "function" other

evalAsInteger :: Value -> Integer
evalAsInteger = \case
  ValueInteger i -> i
  other          -> error $ show $ evalErrorType "integer" other

evalAsSyntax :: Value -> Syntax
evalAsSyntax = \case
    ValueSyntax syntax -> syntax
    other -> error $ show $ evalErrorType "syntax" other

evalAsString :: Value -> Text
evalAsString = \case
    ValueString str -> str
    other           -> error $ show $ evalErrorType "string" other

evalAsMacroAction :: Value -> MacroAction
evalAsMacroAction = \case
    ValueMacroAction macroAction -> macroAction
    other                        -> error $ show $ evalErrorType "macro action" other

evalAsType :: Value -> Ty
evalAsType = \case
    ValueType t -> t
    other       -> error $ show $ evalErrorType "type" other

applyInEnv :: VEnv -> Closure -> Value -> Value
applyInEnv old_env (FO (FOClosure {..})) value =
  let env = Env.insert _closureVar
                       _closureIdent
                       value
                       (_closureEnv <> old_env)
  in evaluateIn env _closureBody
applyInEnv _ (HO prim) value = prim value

apply :: Closure -> Value -> Value
apply (FO (FOClosure {..})) value =
  let env = Env.insert _closureVar
                       _closureIdent
                       value
                       _closureEnv
  in evaluateIn env _closureBody
apply (HO prim) value = prim value

apply' :: VEnv -> Closure -> Value -> Kont -> EState
apply' e (FO (FOClosure{..})) value k = Down (unCore _closureBody) env k
  where env = Env.insert _closureVar
                         _closureIdent
                         value
                         (_closureEnv <> e)
apply' _ (HO prim) value k = Up (prim value) mempty k

-- | predicate to check for done state
final :: EState -> Bool
final (Up _v _env Halt) = True
final _                     = False

-- | Initial state
start :: VEnv -> CoreF TypePattern ConstructorPattern Core -> EState
start e c = Down c e Halt

yield :: EState -> Value
yield (Up v _ Halt) = v
yield _             = error "evaluate: completed impossibly"

extend :: Ident -> Var -> Value -> VEnv -> VEnv
extend i var = Env.insert var i

extends :: [(Ident, Var, Value)] -> VEnv -> VEnv
extends exts env = foldl' (\acc (n,x,v) -> Env.insert x n v acc) env exts

evalErrorType :: Text -> Value -> EvalError
evalErrorType expected got =
  EvalErrorType $ TypeError
    { _typeErrorExpected = expected
    , _typeErrorActual   = describeVal got
    }

doTypeCase :: VEnv -> SrcLoc -> Ty -> [(TypePattern, Core)] -> Value
doTypeCase _ blameLoc v0 [] = error $ show (EvalErrorCase blameLoc (ValueType v0))
doTypeCase env blameLoc (Ty v0) ((p, rhs0) : ps) = match (doTypeCase env blameLoc (Ty v0) ps) p rhs0 v0
  where
    match :: Value -> TypePattern -> Core -> TyF Ty -> Value
    match next (TypePattern t) rhs scrut =
      case (t, scrut) of
        -- unification variables never match; instead, type-case remains stuck
        -- until the variable is unified with a concrete type constructor or a
        -- skolem variable.
        (TyF (TMetaVar _) _, _) -> next
        (_, TyF (TMetaVar _) _) -> next

        (TyF ctor1 args1, TyF ctor2 args2)
          | ctor1 == ctor2 && length args1 == length args2 ->
            evaluateWithExtendedEnv env [ (n, x, ValueType arg)
                                        | (n, x) <- args1
                                        | arg <- args2
                                        ] rhs
        (_, _) -> next
    match _next (AnyType n x) rhs scrut =
      evaluateWithExtendedEnv env [(n, x, ValueType (Ty scrut))] rhs

-- TODO SAT this
doCase :: SrcLoc -> Value -> [(SyntaxPattern, Core)] -> VEnv -> Kont -> EState
doCase blameLoc v0 []               _e _k   = error $ show (EvalErrorCase blameLoc v0)
doCase blameLoc v0 ((p, rhs0) : ps) e  kont = match (doCase blameLoc v0 ps e kont) p rhs0 v0 e kont
  where
    match next (SyntaxPatternIdentifier n x) rhs scrutinee env k =
      case scrutinee of
        v@(ValueSyntax (Syntax (Stx _ _ (Id _)))) ->
          step $ Down (unCore rhs) (extend n x v env) k
        _ -> next
    match next (SyntaxPatternInteger n x) rhs scrutinee env k =
      case scrutinee of
        ValueSyntax (Syntax (Stx _ _ (Integer int))) ->
          step $ Down (unCore rhs) (extend n x (ValueInteger int) env) k
        _ -> next
    match next (SyntaxPatternString n x) rhs scrutinee env k =
      case scrutinee of
        ValueSyntax (Syntax (Stx _ _ (String str))) ->
          step $ Down (unCore rhs) (extend n x (ValueString str) env) k
        _ -> next
    match next SyntaxPatternEmpty rhs scrutinee env k =
      case scrutinee of
        (ValueSyntax (Syntax (Stx _ _ (List [])))) ->
          step $ Down (unCore rhs) env k
        _ -> next
    match next (SyntaxPatternCons nx x nxs xs) rhs scrutinee env k =
      case scrutinee of
        (ValueSyntax (Syntax (Stx scs loc (List (v:vs))))) ->
          let mkEnv = extend nx x (ValueSyntax v)
                    . extend nxs xs (ValueSyntax (Syntax (Stx scs loc (List vs))))
          in step $ Down (unCore rhs) (mkEnv env) k
        _ -> next
    match next (SyntaxPatternList xs) rhs scrutinee env k =
      case scrutinee of
        (ValueSyntax (Syntax (Stx _ _ (List vs))))
          | length vs == length xs ->
            let vals = [ (n, x, ValueSyntax v)
                       | (n,x) <- xs
                       | v     <- vs
                       ]
            in step $ Down (unCore rhs) (vals `extends` env) k
        _ -> next
    match _next SyntaxPatternAny rhs _scrutinee env k =
      step $ Down (unCore rhs) env k

doDataCase :: SrcLoc -> Value -> [(ConstructorPattern, Core)] -> VEnv -> Kont -> EState
doDataCase loc v0 [] _e _kont = error $ show (EvalErrorCase loc v0)
doDataCase loc v0 ((pat, rhs) : ps) env kont =
  match (doDataCase loc v0 ps env kont) (\newEnv -> step $ Down (unCore rhs) newEnv kont) [(unConstructorPattern pat, v0)]
  where
    match
      :: EState {- ^ Failure continuation -}
      -> (VEnv -> EState) {- ^ Success continuation, to be used in an extended environment -}
      -> [(ConstructorPatternF ConstructorPattern, Value)] {- ^ Subpatterns and their scrutinees -}
      -> EState
    match _fk sk [] = sk env
    match fk sk ((CtorPattern ctor subPats, tgt) : more) =
      case tgt of
        ValueCtor c args
          | c == ctor ->
            if length subPats /= length args
              then error $ "Type checker bug: wrong number of pattern vars for constructor " ++ show c
              else match fk sk (zip (map unConstructorPattern subPats) args ++ more)
        _otherValue -> fk
    match fk sk ((PatternVar n x, tgt) : more) =
      match fk (sk . extend n x tgt) more

-- -----------------------------------------------------------------------------
-- Top level API

evaluate :: Core -> Value
evaluate =  evaluateIn mempty

evaluateIn :: VEnv -> Core -> Value
evaluateIn e = yield . until final step . start e . unCore

evaluateWithExtendedEnv :: VEnv -> [(Ident, Var, Value)] -> Core -> Value
evaluateWithExtendedEnv env exts = evaluateIn (inserter exts)
  where
    inserter = foldl' (\acc (n,x,v) -> Env.insert x n v acc) env
