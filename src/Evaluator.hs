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
import Signals
import Syntax
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
  | EvalErrorCase Value
  deriving (Eq, Show)
makePrisms ''EvalError

evalErrorText :: EvalError -> Text
evalErrorText (EvalErrorUnbound x) = "Unbound: " <> T.pack (show x)
evalErrorText (EvalErrorType (TypeError expected got)) =
  "Wrong type. Expected a " <> expected <> " but got a " <> got
evalErrorText (EvalErrorCase val) =
  "Didn't match any pattern: " <> valueText val

newtype Eval a = Eval
   { runEval :: ReaderT VEnv (ExceptT EvalError IO) a }
   deriving (Functor, Applicative, Monad, MonadReader VEnv, MonadError EvalError)

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
  EvalResult { resultEnv :: VEnv
             , resultExpr :: Core
             , resultValue :: Value
             }
  deriving (Eq, Show)

apply :: Closure -> Value -> Eval Value
apply (Closure {..}) value = do
  let env = Env.insert _closureVar
                       _closureIdent
                       value
                       _closureEnv
  withEnv env $ do
    eval _closureBody

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
        ValueClosure $ Closure
          { _closureEnv = Env.insert funVar funIdent vFun env
          , _closureIdent = argIdent
          , _closureVar = argVar
          , _closureBody = def
          }
  withEnv (Env.insert funVar funIdent vFun env) (eval body)
eval (Core (CoreLam ident var body)) = do
  env <- ask
  pure $ ValueClosure $ Closure
    { _closureEnv   = env
    , _closureIdent = ident
    , _closureVar   = var
    , _closureBody  = body
    }
eval (Core (CoreApp fun arg)) = do
  closure <- evalAsClosure fun
  value <- eval arg
  apply closure value
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
eval (Core (CoreSignal signal)) =
  pure $ ValueSignal signal
eval (Core (CoreSyntax syntax)) = do
  pure $ ValueSyntax syntax
eval (Core (CoreCase scrutinee cases)) = do
  v <- eval scrutinee
  doCase v cases
eval (Core (CoreIdentifier (Stx scopeSet srcLoc name))) = do
  pure $ ValueSyntax
       $ Syntax
       $ Stx scopeSet srcLoc
       $ Id name
eval (Core (CoreBool b)) = pure $ ValueBool b
eval (Core (CoreIf b t f)) =
  eval b >>=
  \case
    ValueBool True -> eval t
    ValueBool False -> eval f
    other ->
      throwError $ EvalErrorType $ TypeError
        { _typeErrorExpected = "boolean"
        , _typeErrorActual   = describeVal other
        }
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
        Bool _ ->
          throwError $ EvalErrorType $ TypeError
            { _typeErrorExpected = "id"
            , _typeErrorActual   = "boolean"
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
        Bool _ ->
          throwError $ EvalErrorType $ TypeError
            { _typeErrorExpected = "list"
            , _typeErrorActual   = "boolean"
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
    ValueClosure closure -> do
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

evalAsMacroAction :: Core -> Eval MacroAction
evalAsMacroAction core = do
  value <- eval core
  case value of
    ValueMacroAction macroAction -> pure macroAction
    other -> evalErrorType "macro action" other

withScopeOf :: Core -> ExprF Syntax -> Eval Value
withScopeOf scope expr = do
  scopeSyntax <- evalAsSyntax scope
  case scopeSyntax of
    Syntax (Stx scopeSet loc _) ->
      pure $ ValueSyntax $ Syntax $ Stx scopeSet loc expr

doCase :: Value -> [(Pattern, Core)] -> Eval Value
doCase v0 []               = throwError (EvalErrorCase v0)
doCase v0 ((p, rhs0) : ps) = match (doCase v0 ps) p rhs0 v0
  where
    match next (PatternIdentifier n x) rhs =
      \case
        v@(ValueSyntax (Syntax (Stx _ _ (Id _)))) ->
          withExtendedEnv n x v (eval rhs)
        _ -> next
    match next PatternEmpty rhs =
      \case
        (ValueSyntax (Syntax (Stx _ _ (List [])))) ->
          eval rhs
        _ -> next
    match next (PatternCons nx x nxs xs) rhs =
      \case
        (ValueSyntax (Syntax (Stx scs loc (List (v:vs))))) ->
          withExtendedEnv nx x (ValueSyntax v) $
          withExtendedEnv nxs xs (ValueSyntax (Syntax (Stx scs loc (List vs)))) $
          eval rhs
        _ -> next
    match next (PatternList xs) rhs =
      \case
        (ValueSyntax (Syntax (Stx _ _ (List vs))))
          | length vs == length xs ->
            withManyExtendedEnv [(n, x, (ValueSyntax v))
                                | (n,x) <- xs
                                | v <- vs] $
            eval rhs
        _ -> next
    match _next PatternAny rhs =
      const (eval rhs)
