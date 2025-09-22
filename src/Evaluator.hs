{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  CEK Machine
-- Copyright   :  (c) Jeffrey M. Young
--                    Samuel Gélineau
--                    David Thrane Christiansen
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Jeffrey Young      <jeffrey.young@iohk.io>
--                Samuel Gélineau    <gelisam@gmail.com>
--                David Christiansen <david@davidchristiansen.dk>
-- Stability   :  experimental
--
-- Converting state from the CEK machine to stack trace
-----------------------------------------------------------------------------


{- Note [The CEK interpreter]:

The Klister interpreter is a straightforward implementation of a CEK machine.
The interpreter keeps three kinds of state:

-- C: Control      ::= The thing that is being evaluated
-- E: Environment  ::= The interpreter environment
-- K: Kontinuation ::= The syntactic context of the thing that is being interpreted

Why a CEK? A CEK interpreter allows us to have precise control over the
evaluation of a klister program. For example, because the interpreter keeps a
reference to the kontinuation we can provide stack traces. This handle also
makes a more advanced debugger possible. Upon an evaluation error we could save
the kontinuation stack, over write a variable in the environment a la common
lisp or even rewind the evaluation

See Matthias Felleison's course website for a good reference:
https://felleisen.org/matthias/4400-s20/lecture23.html

The bird's eye view:

The evaluator crawls the input AST and progresses in three modes:

-- 'Down': meaning that the evaluator is searching for a redex to evaluate and
-- therefore moving "down" the AST.

-- 'Up': meaning that the evaluator has evaluated some redex to a value and is
-- passing that value "up" the execution stack.

-- 'Er': meaning that something has gone wrong, the stack is captured and the Er
-- will float up to be handled by the caller of the evaluator.

All interesting things happen by matching on 'Kont', the continuation. This
allows the evaluator to know exactly what needs to happen in order to continue.

-- TODO: #108 describe the how the debugger hooks in

-}

module Evaluator
  ( EvalError (..)
  , EvalResult (..)
  , EState (..)
  , Kont (..)
  , VEnv
  , TypeError (..)
  , evaluate
  , evaluateIn
  , evaluateWithExtendedEnv
  , evalErrorType
  , evalErrorText
  , erroneousValue
  , eStateWith
  , apply
  , doTypeCase
  , try
  , projectKont
  , constructErrorType
  ) where

import Control.Lens hiding (List, elements)
import Control.Exception hiding (TypeError, evaluate)
import Data.Data (Typeable)
import Data.Text (Text)
import qualified Data.Text as T
import Data.List (foldl')

import Datatype
import Core
import Env
import ShortShow
import Syntax
import Syntax.SrcLoc
import Type
import Value

import Debug.Trace
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

data EvalError
  = EvalErrorUnbound Var
  | EvalErrorType TypeError
  | EvalErrorCase SrcLoc Value
  | EvalErrorUser Syntax
  | EvalErrorIdent Value
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
  InArg :: Maybe (Stx Text) -> !Value -> !VEnv -> !Kont -> Kont
  -- ^ The argument is being evaluated, we hold onto meta information in 'Maybe
  -- (Stx Text)' for pretty printing function names. We require that the
  -- function symbol be fully evaluated before evaluating the arguments, hence
  -- the @Value@ is the function closure. The closure does not contain the
  -- function symbol so we must hold onto the meta information to report the
  -- function name in a stack trace. Once the argument is done being evaluated
  -- we pass its value to the closure contained in @Value@ here.
  InFun :: !(CoreF TypePattern ConstructorPattern Core) -> !VEnv -> !Kont -> Kont
  -- ^ The function is being evaluated, so hold onto the argument.

  InLetDef :: !Ident -> !Var -> !(CoreF TypePattern ConstructorPattern Core) -> !VEnv -> !Kont -> Kont
  -- ^ Evaluating the let def

  -- constructors
  InCtor :: ![Value] -> !Constructor -> ![CoreF TypePattern ConstructorPattern Core] -> !VEnv -> !Kont -> Kont

  -- Cases
  InCaseScrut     :: ![(SyntaxPattern, Core)] -> !SrcLoc -> !VEnv -> !Kont -> Kont
  InDataCaseScrut :: ![(ConstructorPattern, Core)] -> !SrcLoc -> !VEnv -> !Kont -> Kont
  InTypeCaseScrut :: ![(TypePattern, Core)] -> !SrcLoc -> !VEnv -> !Kont -> Kont

  {- Note [InCasePattern]
     In case pattern is strictly not necessary, we could do this evaluation in
     the host's runtime instead of in the evaluator but doing so would mean that
     the debugger would not be able to capture the pattern that was matched.
  -}
  InPrim            :: !Text          -> !Kont -> Kont
  InCasePattern     :: !SyntaxPattern -> !Kont -> Kont
  InDataCasePattern :: !ConstructorPattern -> !Kont -> Kont

  -- lists
  InConsHd :: !Core -> !(CoreF TypePattern ConstructorPattern Core) -> !VEnv -> !Kont -> Kont
  InConsTl :: !Core -> !Syntax -> !VEnv -> !Kont -> Kont
  InList   :: !Core -> ![Core] -> ![Syntax] -> !VEnv -> !Kont -> Kont

  -- idents
  InIdent :: !Core -> !VEnv -> !Kont -> Kont
  InIdentEqL :: !HowEq -> !Core -> !VEnv -> !Kont -> Kont
  InIdentEqR :: !Value -> !HowEq -> !VEnv -> !Kont -> Kont

  -- Macros
  InPureMacro :: !VEnv -> !Kont -> Kont
  InBindMacroHd :: !Core -> !VEnv -> !Kont -> Kont
  InBindMacroTl :: !MacroAction -> !VEnv -> !Kont -> Kont

  -- atomics
  InInteger :: !Core -> !VEnv -> !Kont -> Kont
  InString  :: !Core -> !VEnv -> !Kont -> Kont
  InReplaceLocL :: !Core -> !VEnv -> !Kont -> Kont
  InReplaceLocR :: !SrcLoc -> !VEnv -> !Kont -> Kont

  -- scope
  InScope :: !(ExprF Syntax) -> !VEnv -> !Kont -> Kont

  -- logs and errors
  InLog   :: !VEnv -> !Kont -> Kont
  InError :: !VEnv -> !Kont -> Kont

  InSyntaxErrorMessage   :: ![Core] -> !VEnv -> !Kont -> Kont
  InSyntaxErrorLocations :: !Syntax -> ![Core] -> ![Syntax] -> !VEnv -> !Kont -> Kont
  deriving Show

-- | The state of the evaluator
data EState where
  Down :: !(CoreF TypePattern ConstructorPattern Core) -> !VEnv -> !Kont -> EState
  -- ^ 'Down', we are searching the AST for a redex and building up the stack of
  -- continuations
  Up   :: Maybe (Stx Text) -> !Value -> !Kont -> EState
  -- ^ 'Up', means we have performed some evaluation on a redex and are
  -- returning a value up the stack. 'Maybe (Stx Text)' is meta information from
  -- the evaluator used for printing stack traces.
  Er   :: !EvalError -> !VEnv -> !Kont -> EState
  -- ^ 'Er', meaning that we are in an error state and running the debugger
  deriving Show

noStx :: Maybe (Stx Text)
noStx = Nothing

eStateWith :: Value -> EState
eStateWith v = Up noStx v Halt
-- -----------------------------------------------------------------------------
-- The evaluator. The CEK machine is a state machine, the @step@ function moves
-- the state machine a single step of evaluation. This is the heart of the
-- evaluator.


-- | Make a single step transition in the CEK state machine.
step :: EState -> EState
step done@(Up _ _val Halt) = done

-- for now we just bail out. Once we have a debugger we'll do something more
-- advanced.
step done@(Er _err _env _k)  = done

-- Upsweep, returning a value after evaluating a redex
step (Up stx v k) =
  case k of
    -- functions
    -- we evaluated the arg to get a closed so now we evaluate the fun
    (InArg st fun env kont) -> applyAsClosure st env fun v kont
    -- we evaluated the fun so now do the application
    (InFun arg env kont)  -> Down arg env (InArg stx v env kont)

    -- lets
    -- we have the value for the def, now eval the body
    (InLetDef id' var body env kont) -> Down body (extend id' var v env) kont

    -- done, FIXME use a banker's queue instead of a list
    (InCtor v_args c [] _env kont) -> Up stx (ValueCtor c (reverse $ v : v_args)) kont
    -- still processing
    (InCtor vs c (a:as) env kont) -> Down a env (InCtor (v:vs) c as env kont)


    -- Cases
    (InCaseScrut cs loc env kont)     -> doCase loc v cs env kont
    (InDataCaseScrut cs loc env kont) -> doDataCase loc v cs env kont
    (InTypeCaseScrut cs loc env kont) ->
      evalAsType v
      (\good -> Up stx (ValueMacroAction $ MacroActionTypeCase env loc good cs) kont)
      (\err  -> Er err env kont)

    -- Case passthroughs, see the Note [InCasePattern]
    (InPrim _ kont)                   -> Up stx v kont
    (InCasePattern _ kont)            -> Up stx v kont
    (InDataCasePattern _ kont)        -> Up stx v kont

    -- Idents
    (InIdent scope env kont) -> case v of
      ValueSyntax sx ->
        case _unSyntax sx of
          (Stx _ _ expr) -> case expr of
            Integer _ ->
              Er (EvalErrorType
                   $ TypeError { _typeErrorExpected = "id"
                               , _typeErrorActual   = "integer"
                               }) env k
            String _ ->
              Er (EvalErrorType
                  $ TypeError { _typeErrorExpected = "id"
                              , _typeErrorActual   = "string"
                              }) env k
            List _ ->
              Er (EvalErrorType
                  $ TypeError { _typeErrorExpected = "id"
                              , _typeErrorActual   = "list"
                              }) env k
            name@(Id _) -> Down (unCore scope) env (InScope name env kont)
      other -> Er (EvalErrorIdent other) env k
    (InIdentEqL how r env kont)  -> Down (unCore r) env (InIdentEqR v how env kont)
    (InIdentEqR how lv _env kont) -> Up stx (ValueMacroAction $ MacroActionIdentEq lv how v) kont

    -- Short circuit to speed this up, we could issue an Down and do this recursively
    (InScope expr env kont) ->
      evalAsSyntax v
      (\(Syntax (Stx scopeSet loc _)) -> Up stx (ValueSyntax $ Syntax $ Stx scopeSet loc expr) kont)
      (\err                           -> Er err env kont)


    -- pairs
    (InConsHd scope tl env kont) ->
      evalAsSyntax v
      (\good -> Down tl env (InConsTl scope good env kont))
      (\err  -> Er err env kont)
    (InConsTl scope hd env kont) ->
      evalAsSyntax v
      (\(Syntax (Stx _ _ expr)) ->
          case expr of
            List tl -> Down (unCore scope) env (InScope (List $ hd : tl) env kont)
            String _ ->
              Er (EvalErrorType
                   $ TypeError { _typeErrorExpected = "list"
                               , _typeErrorActual   = "string"
                               }) env k
            Id _ -> Er (EvalErrorType
                        $ TypeError { _typeErrorExpected = "list"
                                    , _typeErrorActual   = "id"
                                    }) env k
            Integer _ -> Er (EvalErrorType
                             $ TypeError { _typeErrorExpected = "list"
                                         , _typeErrorActual   = "integer"
                                         }) env k
         )
      (\err -> Er err env kont)


    -- lists
    -- base case
    (InList scope [] dones env kont) ->
      evalAsSyntax v
      (\good -> Down (unCore scope) env (InScope (List $ reverse $ good : dones) env kont))
      (\err  -> Er err env kont)
    -- still some todo
    (InList scope (el:els) dones env kont) ->
      evalAsSyntax v
      (\good -> Down (unCore el) env (InList scope els (good : dones) env kont))
      (\err  -> Er err env kont)


    -- Macros
    (InPureMacro _env kont) -> Up stx (ValueMacroAction $ MacroActionPure v) kont
    (InBindMacroHd tl env kont) ->
      evalAsMacroAction v
      (\good -> Down (unCore tl) env (InBindMacroTl good env kont))
      (\err  -> Er err env kont)

    (InBindMacroTl macroAction env kont) ->
      evalAsClosure v
      (\good -> Up stx (ValueMacroAction $ MacroActionBind macroAction good) kont)
      (\err  -> Er err env kont)


    -- Syntax and Atomics
    (InInteger scope env kont) ->
      evalAsInteger v
      (\good -> Down (unCore scope) env (InScope (Integer good) env kont))
      (\err  -> Er err env kont)
    (InString scope env kont) ->
      evalAsString v
      (\good -> Down (unCore scope) env (InScope (String good) env kont))
      (\err  -> Er err env kont)
    (InReplaceLocL sx env kont) ->
      evalAsSyntax v
      (\(Syntax (Stx _ newLoc _)) -> Down (unCore sx) env (InReplaceLocR newLoc env kont) )
      (\err -> Er err env kont)
    (InReplaceLocR loc env kont) ->
      evalAsSyntax v
      (\(Syntax (Stx scs _ contents)) -> Up stx (ValueSyntax $ Syntax $ Stx scs loc contents) kont)
      (\err -> Er err env kont)
    (InLog   env kont)   ->
      evalAsSyntax v
      (\good -> Up stx (ValueMacroAction (MacroActionLog good)) kont)
      (\err  -> Er err env kont)


    -- Errors
    (InError env kont) ->
      evalAsSyntax v
      (\good -> Er (EvalErrorUser good) env kont)
      (\err  -> Er err env kont)
    (InSyntaxErrorMessage locs env kont) ->
      evalAsSyntax v
      (\msg_syn ->
         case locs of
           -- done
           []     -> Up stx (ValueMacroAction $ MacroActionSyntaxError
                            (SyntaxError { _syntaxErrorMessage   = msg_syn
                                         , _syntaxErrorLocations = mempty
                                         })) kont
           (l:ls) -> Down (unCore l) env (InSyntaxErrorLocations msg_syn ls mempty env kont)
          )
      (\err -> Er err env kont)
    -- done
    (InSyntaxErrorLocations msg_syn [] dones _env kont) ->
        Up stx (ValueMacroAction
                $ MacroActionSyntaxError (SyntaxError { _syntaxErrorMessage   = msg_syn
                                                      , _syntaxErrorLocations = dones
                                                      })) kont
    (InSyntaxErrorLocations msg (l:ls) dones env kont) ->
      evalAsSyntax v
      (\good -> Down (unCore l) env (InSyntaxErrorLocations msg ls (good : dones) env kont))
      (\err  -> Er err env kont)

-- the downsweep, searching for a redex to evaluate.
step (Down c env k)  =
  case c of

    -- atoms
    (CoreString s)    -> Up noStx (ValueString s) k
    (CoreInteger i)   -> Up noStx (ValueInteger i) k
    (CoreIntegerSyntax (ScopedInteger int scope)) -> Down (unCore int) env (InInteger scope env k)
    (CoreStringSyntax  (ScopedString  str scope)) -> Down (unCore str) env (InString scope env k)
    (CoreSyntax s)    -> Up noStx (ValueSyntax s) k
    (CoreError what)  -> Down (unCore what) env (InError env k)
    (CoreEmpty (ScopedEmpty scope)) -> Down (unCore scope) env (InScope (List mempty) env k)
    CoreMakeIntroducer -> Up noStx (ValueMacroAction MacroActionIntroducer)   k
    CoreWhichProblem   -> Up noStx (ValueMacroAction MacroActionWhichProblem) k


    -- variables and binders
    (CoreVar var) ->
      case Env.lookup var env of
        Just (i,val) -> Up (Just i) val k
        _        -> Er (EvalErrorUnbound var) env k

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
                           []     -> Up noStx (ValueCtor con mempty) k
                           -- process fields left to right
                           (f:fs) -> Down (unCore f) env (InCtor mempty con (fmap unCore fs) env k)


    -- lambdas and application
    (CoreLam ident var body) ->
      let lam = ValueClosure $ FO $ FOClosure
            { _closureEnv   = env
            , _closureIdent = ident
            , _closureVar   = var
            , _closureBody  = body
            }
      in Up noStx lam k
    (CoreApp fun arg) -> Down (unCore fun) env (InFun (unCore arg) env k)


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
    (CoreReplaceLoc loc stx) -> Down (unCore loc) env (InReplaceLocL stx env k)


    -- macros
    (CorePureMacro arg)   -> Down (unCore arg) env (InPureMacro env k)
    (CoreBindMacro hd tl) -> Down (unCore hd) env (InBindMacroHd tl env k)


    -- others
    (CoreLog msg)      -> Down (unCore msg) env (InLog env k)
    (CoreSyntaxError err) ->
      Down (unCore $ _syntaxErrorMessage err) env (InSyntaxErrorMessage (_syntaxErrorLocations err) env k)


-- -----------------------------------------------------------------------------
-- Helper Functions

evalErrorText :: EvalError -> Text
evalErrorText (EvalErrorUnbound x) = "Unbound: " <> T.pack (show x)
evalErrorText (EvalErrorType (TypeError expected got)) =
  "Wrong type. Expected a " <> expected <> " but got a " <> got
evalErrorText (EvalErrorCase loc val) =
  "Didn't match any pattern at " <> T.pack (shortShow loc) <> ": " <> valueText val
evalErrorText (EvalErrorUser what) =
  T.pack (shortShow (stxLoc what)) <> ":\n\t" <>
  syntaxText what
evalErrorText (EvalErrorIdent v) = "Attempt to bind identifier to non-value: " <> valueText v

type ContinueWith a = a -> EState
type OnFailure   = EvalError -> EState

evalAsClosure :: Value -> ContinueWith Closure -> OnFailure -> EState
evalAsClosure closure_to_be on_success on_error =
  case closure_to_be of
    ValueClosure closure -> on_success closure
    other -> on_error (evalErrorType "function" other)

evalAsInteger :: Value -> ContinueWith Integer -> OnFailure -> EState
evalAsInteger int_to_be on_success on_error =
  case int_to_be of
    ValueInteger i -> on_success i
    other          -> on_error (evalErrorType "integer" other)

evalAsSyntax :: Value -> ContinueWith Syntax -> OnFailure -> EState
evalAsSyntax syn_to_be on_success on_error =
  case syn_to_be of
    ValueSyntax syntax -> on_success syntax
    other              -> on_error (evalErrorType "syntax" other)

evalAsString :: Value -> ContinueWith Text -> OnFailure -> EState
evalAsString str_to_be on_success on_error =
  case str_to_be of
    ValueString str -> on_success str
    other           -> on_error (evalErrorType "string" other)

evalAsMacroAction :: Value -> (MacroAction -> EState) -> (EvalError -> EState) -> EState
evalAsMacroAction v on_success on_error = case v of
    ValueMacroAction macroAction -> on_success macroAction
    other                        -> on_error (evalErrorType "macro action" other)

evalAsType :: Value -> ContinueWith Ty -> OnFailure -> EState
evalAsType v on_success on_error =
  case v of
    ValueType t -> on_success t
    other       -> on_error (evalErrorType "type" other)

apply :: Closure -> Value -> Either EState Value
apply (FO (FOClosure {..})) value =
  let env = Env.insert _closureVar
                       _closureIdent
                       value
                       _closureEnv
  in evaluateIn env _closureBody
apply (HO _n prim) value = return $! prim value

applyAsClosure :: Maybe (Stx Text) -> VEnv -> Value -> Value -> Kont -> EState
applyAsClosure stx e v_closure value k = case v_closure of
    ValueClosure closure -> app closure
    other                -> Er (evalErrorType "function" other) e k

    where app (FO (FOClosure{..})) =
            let env = Env.insert _closureVar _closureIdent value _closureEnv
            in Down (unCore _closureBody) env k
          app (HO n prim)            = Up stx (prim value) (InPrim n k)

-- | predicate to check for done state
final :: EState -> Bool
final (Up _ _v Halt)      = True
final (Er _err _env _k) = True
final _                 = False

-- | Initial state
start :: VEnv -> CoreF TypePattern ConstructorPattern Core -> EState
start e c = trace ("Core: " ++ show c) $ trace ("Env: " ++ show e) $ Down c e Halt

yield :: EState -> Either EState Value
yield (Up _ v Halt) = Right v
yield e@Er{}      = Left  e
yield _           = error "evaluate: completed impossibly"

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

-- this is a copy of 'evalErrorType' but with no memory of how we got to this
-- error state. This should just be a stopgap and we should remove it. Its sole
-- use case is in the expander where we have redundant error checks due to
-- functions such as @doTypeCase@
constructErrorType :: Text -> Value -> EState
constructErrorType expected got = Er err mempty Halt
  where
    err = EvalErrorType $ TypeError
      { _typeErrorExpected = expected
      , _typeErrorActual   = describeVal got
      }

doTypeCase :: VEnv -> SrcLoc -> Ty -> [(TypePattern, Core)] -> Either EState Value
-- We pass @Right $ ValueType v0@ here so that the Core type-case still matches
-- on the outermost constructor instead of failing immedaitely. This behavior
-- comports with the other cases and could allow a debugger to fixup an
-- expression while knowing the type-case.
doTypeCase _env _blameLoc v0 [] = Right $ ValueType v0
doTypeCase env blameLoc (Ty v0) ((p, rhs0) : ps) =
  do v <- doTypeCase env blameLoc (Ty v0) ps
     match v p rhs0 v0
  where
    match :: Value -> TypePattern -> Core -> TyF Ty -> Either EState Value
    match next (TypePattern t) rhs scrut =
      case (t, scrut) of
        -- unification variables never match; instead, type-case remains stuck
        -- until the variable is unified with a concrete type constructor or a
        -- skolem variable.
        (TyF (TMetaVar _) _, _) -> return next
        (_, TyF (TMetaVar _) _) -> return next

        (TyF ctor1 args1, TyF ctor2 args2)
          | ctor1 == ctor2 && length args1 == length args2 ->
            evaluateWithExtendedEnv env [ (n, x, ValueType arg)
                                        | (n, x) <- args1
                                        | arg <- args2
                                        ] rhs
        (_, _) -> return next
    match _next (AnyType n x) rhs scrut =
      evaluateWithExtendedEnv env [(n, x, ValueType (Ty scrut))] rhs

-- TODO SAT this
doCase :: SrcLoc -> Value -> [(SyntaxPattern, Core)] -> VEnv -> Kont -> EState
doCase blameLoc v0 []               e  kont = Er (EvalErrorCase blameLoc v0) e kont
doCase blameLoc v0 ((p, rhs0) : ps) e  kont = match (doCase blameLoc v0 ps e kont) p rhs0 v0 e kont
  where
    match next pat@(SyntaxPatternIdentifier n x) rhs scrutinee env k =
      case scrutinee of
        v@(ValueSyntax (Syntax (Stx _ _ (Id _)))) ->
          step $ Down (unCore rhs) (extend n x v env) (InCasePattern pat k)
        _ -> next
    match next pat@(SyntaxPatternInteger n x) rhs scrutinee env k =
      case scrutinee of
        ValueSyntax (Syntax (Stx _ _ (Integer int))) ->
          step $ Down (unCore rhs) (extend n x (ValueInteger int) env) (InCasePattern pat k)
        _ -> next
    match next pat@(SyntaxPatternString n x) rhs scrutinee env k =
      case scrutinee of
        ValueSyntax (Syntax (Stx _ _ (String str))) ->
          step $ Down (unCore rhs) (extend n x (ValueString str) env) (InCasePattern pat k)
        _ -> next
    match next SyntaxPatternEmpty rhs scrutinee env k =
      case scrutinee of
        (ValueSyntax (Syntax (Stx _ _ (List [])))) ->
          step $ Down (unCore rhs) env (InCasePattern SyntaxPatternEmpty k)
        _ -> next
    match next pat@(SyntaxPatternCons nx x nxs xs) rhs scrutinee env k =
      case scrutinee of
        (ValueSyntax (Syntax (Stx scs loc (List (v:vs))))) ->
          let mkEnv = extend nx x (ValueSyntax v)
                    . extend nxs xs (ValueSyntax (Syntax (Stx scs loc (List vs))))
          in step $ Down (unCore rhs) (mkEnv env) (InCasePattern pat k)
        _ -> next
    match next pat@(SyntaxPatternList xs) rhs scrutinee env k =
      case scrutinee of
        (ValueSyntax (Syntax (Stx _ _ (List vs))))
          | length vs == length xs ->
            let vals = [ (n, x, ValueSyntax v)
                       | (n,x) <- xs
                       | v     <- vs
                       ]
            in step $ Down (unCore rhs) (vals `extends` env) (InCasePattern pat k)
        _ -> next
    match _next SyntaxPatternAny rhs _scrutinee env k =
      step $ Down (unCore rhs) env (InCasePattern SyntaxPatternAny k)

doDataCase :: SrcLoc -> Value -> [(ConstructorPattern, Core)] -> VEnv -> Kont -> EState
doDataCase loc v0 [] env kont = Er (EvalErrorCase loc v0) env kont
doDataCase loc v0 ((pat, rhs) : ps) env kont =
  match (doDataCase loc v0 ps env kont) (\newEnv -> step $ Down (unCore rhs) newEnv (InDataCasePattern pat kont)) [(unConstructorPattern pat, v0)]
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

evaluate :: Core -> Either EState Value
evaluate =  evaluateIn mempty

evaluateIn :: VEnv -> Core -> Either EState Value
evaluateIn e = yield . until final step . start e . unCore

evaluateWithExtendedEnv :: VEnv -> [(Ident, Var, Value)] -> Core -> Either EState Value
evaluateWithExtendedEnv env exts = evaluateIn (inserter exts)
  where
    inserter = foldl' (\acc (n,x,v) -> Env.insert x n v acc) env

erroneousValue :: EvalError -> Value
erroneousValue (EvalErrorCase _loc v) = v
erroneousValue (EvalErrorIdent v)     = v
erroneousValue  _                     =
  error $ mconcat [ "erroneousValue: "
                  , "Evaluator concluded in an error that did not return a value"
                  ]

projectKont :: EState -> Kont
projectKont (Er _ _ k)   = k
projectKont (Up _ _ k)     = k
projectKont (Down _ _ k) = k
