{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
module Evaluator where

import Control.Lens hiding (List, elements)
import Control.Monad.Except
import Control.Monad.Reader
import Data.Text (Text)
import qualified Data.Text as T

import Core
import Env
import ShortShow
import Signals
import Syntax
import Syntax.SrcLoc
import Type
import Value

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
  deriving (Show)
makePrisms ''EvalError

evalErrorText :: EvalError -> Text
evalErrorText (EvalErrorUnbound x) = "Unbound: " <> T.pack (show x)
evalErrorText (EvalErrorType (TypeError expected got)) =
  "Wrong type. Expected a " <> expected <> " but got a " <> got
evalErrorText (EvalErrorCase loc val) =
  "Didn't match any pattern at " <> T.pack (shortShow loc) <> ": " <> valueText val
evalErrorText (EvalErrorUser what) =
  T.pack (shortShow (stxLoc what)) <> ":\n\t" <>
  syntaxText what

newtype Eval a = Eval
   { runEval :: ReaderT VEnv (ExceptT EvalError IO) a }
   deriving (Functor, Applicative, Monad,
             MonadReader VEnv, MonadError EvalError,
             MonadIO)

withEnv :: VEnv -> Eval a -> Eval a
withEnv = local . const

withExtendedEnv :: Ident -> Var -> Value -> Eval a -> Eval a
withExtendedEnv n x v act = local (Env.insert x n v) act

withManyExtendedEnv :: [(Ident, Var, Value)] -> Eval a -> Eval a
withManyExtendedEnv exts act = local (inserter exts) act
  where
    inserter [] = id
    inserter ((n, x, v) : rest) = Env.insert x n v . inserter rest

-- | 'resultValue' is the result of evaluating the 'resultExpr' in 'resultCtx'
data EvalResult =
  EvalResult { resultLoc :: SrcLoc
             , resultEnv :: VEnv
             , resultExpr :: Core
             , resultType :: Scheme Ty
             , resultValue :: Value
             }

apply :: Closure -> Value -> Eval Value
apply (FO (FOClosure {..})) value = do
  let env = Env.insert _closureVar
                       _closureIdent
                       value
                       _closureEnv
  withEnv env $
    eval _closureBody
apply (HO prim) value = pure (prim value)

eval :: Core -> Eval Value
eval (Core (CoreVar var)) = do
  env <- ask
  case lookupVal var env of
    Just value -> pure value
    _ -> throwError $ EvalErrorUnbound var
eval (Core (CoreLet ident var def body)) = do
  val <- eval def
  env <- ask
  withEnv (Env.insert var ident val env) (eval body)
eval (Core (CoreLetFun funIdent funVar argIdent argVar def body)) = do
  env <- ask
  let vFun =
        ValueClosure $ FO $ FOClosure
          { _closureEnv = Env.insert funVar funIdent vFun env
          , _closureIdent = argIdent
          , _closureVar = argVar
          , _closureBody = def
          }
  withEnv (Env.insert funVar funIdent vFun env) (eval body)
eval (Core (CoreLam ident var body)) = do
  env <- ask
  pure $ ValueClosure $ FO $ FOClosure
    { _closureEnv   = env
    , _closureIdent = ident
    , _closureVar   = var
    , _closureBody  = body
    }
eval (Core (CoreApp fun arg)) = do
  closure <- evalAsClosure fun
  value <- eval arg
  apply closure value
eval (Core (CoreCtor c args)) =
  ValueCtor c <$> traverse eval args
eval (Core (CoreDataCase loc scrut cases)) = do
  value <- eval scrut
  doDataCase loc value cases
eval (Core (CoreString str)) = pure (ValueString str)
eval (Core (CoreError what)) = do
  msg <- evalAsSyntax what
  throwError $ EvalErrorUser msg
eval (Core (CorePure arg)) = do
  value <- eval arg
  pure $ ValueMacroAction
       $ MacroActionPure value
eval (Core (CoreBind hd tl)) = do
  macroAction <- evalAsMacroAction hd
  closure <- evalAsClosure tl
  pure $ ValueMacroAction
       $ MacroActionBind macroAction closure
eval (Core (CoreSyntaxError syntaxErrorExpr)) = do
  syntaxErrorValue <- traverse evalAsSyntax syntaxErrorExpr
  pure $ ValueMacroAction
       $ MacroActionSyntaxError syntaxErrorValue
eval (Core (CoreSendSignal signalExpr)) = do
  theSignal <- evalAsSignal signalExpr
  pure $ ValueMacroAction
       $ MacroActionSendSignal theSignal
eval (Core (CoreWaitSignal signalExpr)) = do
  theSignal <- evalAsSignal signalExpr
  pure $ ValueMacroAction
       $ MacroActionWaitSignal theSignal
eval (Core (CoreIdentEq how e1 e2)) =
  ValueMacroAction <$> (MacroActionIdentEq how <$> eval e1 <*> eval e2)
eval (Core (CoreLog msg)) = do
  msgVal <- evalAsSyntax msg
  return $ ValueMacroAction (MacroActionLog msgVal)
eval (Core CoreMakeIntroducer) =
  return $ ValueMacroAction MacroActionIntroducer
eval (Core CoreWhichProblem) = do
  return $ ValueMacroAction MacroActionWhichProblem
eval (Core (CoreSignal signal)) =
  pure $ ValueSignal signal
eval (Core (CoreSyntax syntax)) = do
  pure $ ValueSyntax syntax
eval (Core (CoreCase loc scrutinee cases)) = do
  v <- eval scrutinee
  doCase loc v cases
eval (Core (CoreIdentifier (Stx scopeSet srcLoc name))) = do
  pure $ ValueSyntax
       $ Syntax
       $ Stx scopeSet srcLoc
       $ Id name
eval (Core (CoreIdent (ScopedIdent ident scope))) = do
  identSyntax <- evalAsSyntax ident
  case identSyntax of
    Syntax (Stx _ _ expr) ->
      case expr of
        Sig _ ->
          throwError $ EvalErrorType $ TypeError
            { _typeErrorExpected = "id"
            , _typeErrorActual   = "signal"
            }
        String _ ->
          throwError $ EvalErrorType $ TypeError
            { _typeErrorExpected = "id"
            , _typeErrorActual   = "string"
            }
        List _ ->
          throwError $ EvalErrorType $ TypeError
            { _typeErrorExpected = "id"
            , _typeErrorActual   = "list"
            }
        Id name -> withScopeOf scope $ Id name
eval (Core (CoreEmpty (ScopedEmpty scope))) = withScopeOf scope (List [])
eval (Core (CoreCons (ScopedCons hd tl scope))) = do
  hdSyntax <- evalAsSyntax hd
  tlSyntax <- evalAsSyntax tl
  case tlSyntax of
    Syntax (Stx _ _ expr) ->
      case expr of
        List vs -> withScopeOf scope $ List $ hdSyntax : vs
        String _ ->
          throwError $ EvalErrorType $ TypeError
            { _typeErrorExpected = "list"
            , _typeErrorActual   = "string"
            }
        Id _ ->
          throwError $ EvalErrorType $ TypeError
            { _typeErrorExpected = "list"
            , _typeErrorActual   = "id"
            }
        Sig _ ->
          throwError $ EvalErrorType $ TypeError
            { _typeErrorExpected = "list"
            , _typeErrorActual   = "signal"
            }
eval (Core (CoreList (ScopedList elements scope))) = do
  vec <- List <$> traverse evalAsSyntax elements
  withScopeOf scope vec
eval (Core (CoreStringSyntax (ScopedString str scope))) = do
  strV <- evalAsString str
  withScopeOf scope (String strV)
eval (Core (CoreReplaceLoc loc stx)) = do
  Syntax (Stx _ newLoc _) <- evalAsSyntax loc
  Syntax (Stx scs _ contents) <- evalAsSyntax stx
  return $ ValueSyntax $ Syntax $ Stx scs newLoc contents
eval (Core (CoreTypeCase loc scrut cases)) = do
  ty <- evalAsType scrut
  env <- ask
  return $ ValueMacroAction $ MacroActionTypeCase env loc ty cases

evalErrorType :: Text -> Value -> Eval a
evalErrorType expected got =
  throwError $ EvalErrorType $ TypeError
    { _typeErrorExpected = expected
    , _typeErrorActual   = describeVal got
    }

evalAsClosure :: Core -> Eval Closure
evalAsClosure core = do
  value <- eval core
  case value of
    ValueClosure closure ->
      pure closure
    other -> evalErrorType "function" other

evalAsSignal :: Core -> Eval Signal
evalAsSignal core = do
  value <- eval core
  case value of
    ValueSignal s -> pure s
    other -> evalErrorType "signal" other

evalAsSyntax :: Core -> Eval Syntax
evalAsSyntax core = do
  value <- eval core
  case value of
    ValueSyntax syntax -> pure syntax
    other -> evalErrorType "syntax" other

evalAsString :: Core -> Eval Text
evalAsString core = do
  value <- eval core
  case value of
    ValueString str -> pure str
    other -> evalErrorType "string" other

evalAsMacroAction :: Core -> Eval MacroAction
evalAsMacroAction core = do
  value <- eval core
  case value of
    ValueMacroAction macroAction -> pure macroAction
    other -> evalErrorType "macro action" other

evalAsType :: Core -> Eval Ty
evalAsType core = do
  value <- eval core
  case value of
    ValueType t -> pure t
    other -> evalErrorType "type" other

withScopeOf :: Core -> ExprF Syntax -> Eval Value
withScopeOf scope expr = do
  scopeSyntax <- evalAsSyntax scope
  case scopeSyntax of
    Syntax (Stx scopeSet loc _) ->
      pure $ ValueSyntax $ Syntax $ Stx scopeSet loc expr

doDataCase :: SrcLoc -> Value -> [(ConstructorPattern, Core)] -> Eval Value
doDataCase loc v0 [] = throwError (EvalErrorCase loc v0)
doDataCase loc v0 ((pat, rhs) : ps) = match (doDataCase loc v0 ps) pat
  where
    match next (ConstructorPattern ctor vars) =
      case v0 of
        ValueCtor c args
          | c == ctor ->
            if length vars /= length args
              then error $ "Type checker bug: wrong number of pattern vars for constructor " ++ show c
              else withManyExtendedEnv [ (n, x, v) | (n, x) <- vars
                                       | v <- args
                                       ] $
                   eval rhs
          | otherwise -> next
        _otherValue -> next
    match _next (AnyConstructor n x) =
      withExtendedEnv n x v0 $ eval rhs

doTypeCase :: SrcLoc -> Ty -> [(TypePattern, Core)] -> Eval Value
doTypeCase blameLoc v0 [] = throwError (EvalErrorCase blameLoc (ValueType v0))
doTypeCase blameLoc (Ty v0) ((p, rhs0) : ps) = match (doTypeCase blameLoc (Ty v0) ps) p rhs0 v0
  where
    match :: Eval Value -> TypePattern -> Core -> TyF Ty -> Eval Value
    match next (TypePattern t) rhs scrut =
      case (t, scrut) of
        -- unification variables never match; instead, type-case remains stuck
        -- until the variable is unified with a concrete type constructor or a
        -- skolem variable.
        (TyF (TMetaVar _) _, _) -> next
        (_, TyF (TMetaVar _) _) -> next

        (TyF ctor1 args1, TyF ctor2 args2)
          | ctor1 == ctor2 && length args1 == length args2 ->
            withManyExtendedEnv [(n, x, ValueType arg) | (n, x) <- args1, arg <- args2] $
            eval rhs
        (_, _) -> next
    match _next (AnyType n x) rhs scrut =
      withExtendedEnv n x (ValueType (Ty scrut)) (eval rhs)

doCase :: SrcLoc -> Value -> [(SyntaxPattern, Core)] -> Eval Value
doCase blameLoc v0 []               = throwError (EvalErrorCase blameLoc v0)
doCase blameLoc v0 ((p, rhs0) : ps) = match (doCase blameLoc v0 ps) p rhs0 v0
  where
    match next (SyntaxPatternIdentifier n x) rhs =
      \case
        v@(ValueSyntax (Syntax (Stx _ _ (Id _)))) ->
          withExtendedEnv n x v (eval rhs)
        _ -> next
    match next (SyntaxPatternString n x) rhs =
      \case
        ValueSyntax (Syntax (Stx _ _ (String str))) ->
          withExtendedEnv n x (ValueString str) (eval rhs)
        _ -> next
    match next SyntaxPatternEmpty rhs =
      \case
        (ValueSyntax (Syntax (Stx _ _ (List [])))) ->
          eval rhs
        _ -> next
    match next (SyntaxPatternCons nx x nxs xs) rhs =
      \case
        (ValueSyntax (Syntax (Stx scs loc (List (v:vs))))) ->
          withExtendedEnv nx x (ValueSyntax v) $
          withExtendedEnv nxs xs (ValueSyntax (Syntax (Stx scs loc (List vs)))) $
          eval rhs
        _ -> next
    match next (SyntaxPatternList xs) rhs =
      \case
        (ValueSyntax (Syntax (Stx _ _ (List vs))))
          | length vs == length xs ->
            withManyExtendedEnv [(n, x, (ValueSyntax v))
                                | (n,x) <- xs
                                | v <- vs] $
            eval rhs
        _ -> next
    match _next SyntaxPatternAny rhs =
      const (eval rhs)
