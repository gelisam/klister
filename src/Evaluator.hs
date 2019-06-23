{-# LANGUAGE GeneralizedNewtypeDeriving, LambdaCase, RecordWildCards #-}
module Evaluator where

import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as Map

import Syntax
import Core
import Value


-- TODO: more precise representation
type Type = String

data TypeError = TypeError
  { typeErrorExpected :: Type
  , typeErrorActual   :: Type
  }

data Error
  = ErrorSyntax SyntaxError
  | ErrorUnbound Var
  | ErrorType TypeError
  | ErrorCase Value

newtype Eval a = Eval
   { runEval :: ReaderT Env (ExceptT Error IO) a }
   deriving (Functor, Applicative, Monad, MonadReader Env, MonadError Error)

withEnv :: Env -> Eval a -> Eval a
withEnv = local . const

withExtendedEnv :: Ident -> Var -> Value -> Eval a -> Eval a
withExtendedEnv n x v act = local (Map.insert x (n, v)) act

withManyExtendedEnv :: [(Ident, Var, Value)] -> Eval a -> Eval a
withManyExtendedEnv exts act = local (inserter exts) act
  where
    inserter [] = id
    inserter ((n, x, v) : rest) = Map.insert x (n, v) . inserter rest


eval :: Core -> Eval Value
eval (Core (CoreVar var)) = do
  env <- ask
  case Map.lookup var env of
    Just (_ident, value) -> pure value
    _ -> throwError $ ErrorUnbound var
eval (Core (CoreLam ident var body)) = do
  env <- ask
  pure $ ValueClosure $ Closure
    { closureEnv   = env
    , closureIdent = ident
    , closureVar   = var
    , closureBody  = body
    }
eval (Core (CoreApp fun arg)) = do
  funValue <- eval fun
  argValue <- eval arg
  case funValue of
    ValueClosure (Closure {..}) -> do
      let env = Map.insert closureVar
                           (closureIdent, argValue)
                           closureEnv
      withEnv env $ do
        eval closureBody
    ValueSyntax _ -> do
      throwError $ ErrorType $ TypeError
        { typeErrorExpected = "function"
        , typeErrorActual   = "syntax"
        }
eval (Core (CoreSyntaxError syntaxError)) = do
  throwError $ ErrorSyntax syntaxError
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
eval (Core (CoreIdent (ScopedIdent ident scope))) = do
  identSyntax <- evalAsSyntax ident
  case identSyntax of
    Syntax (Stx _ _ expr) -> case expr of
      List _ -> do
        throwError $ ErrorType $ TypeError
          { typeErrorExpected = "id"
          , typeErrorActual   = "list"
          }
      Vec _ -> do
        throwError $ ErrorType $ TypeError
          { typeErrorExpected = "id"
          , typeErrorActual   = "vec"
          }
      Id name -> withScopeOf scope $ Id name
eval (Core (CoreEmpty (ScopedEmpty scope))) = withScopeOf scope (List [])
eval (Core (CoreCons (ScopedCons hd tl scope))) = do
  hdSyntax <- evalAsSyntax hd
  tlSyntax <- evalAsSyntax tl
  case tlSyntax of
    Syntax (Stx _ _ expr) -> case expr of
      List vs -> withScopeOf scope $ List $ hdSyntax : vs
      Vec _ -> do
        throwError $ ErrorType $ TypeError
          { typeErrorExpected = "list"
          , typeErrorActual   = "vec"
          }
      Id _ -> do
        throwError $ ErrorType $ TypeError
          { typeErrorExpected = "list"
          , typeErrorActual   = "id"
          }
eval (Core (CoreVec (ScopedVec elements scope))) = do
  vec <- Vec <$> traverse evalAsSyntax elements
  withScopeOf scope vec

evalAsSyntax :: Core -> Eval Syntax
evalAsSyntax core = do
  value <- eval core
  case value of
    ValueClosure _ -> do
      throwError $ ErrorType $ TypeError
        { typeErrorExpected = "syntax"
        , typeErrorActual = "function"
        }
    ValueSyntax syntax -> pure syntax

withScopeOf :: Core -> ExprF Syntax -> Eval Value
withScopeOf scope expr = do
  scopeSyntax <- evalAsSyntax scope
  case scopeSyntax of
    Syntax (Stx scopeSet loc _) ->
      pure $ ValueSyntax $ Syntax $ Stx scopeSet loc expr

doCase :: Value -> [(Pattern, Core)] -> Eval Value
doCase v0 []               = throwError (ErrorCase v0)
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
    match next (PatternVec xs) rhs =
      \case
        (ValueSyntax (Syntax (Stx _ _ (Vec vs))))
          | length vs == length xs ->
            withManyExtendedEnv [(n, x, (ValueSyntax v)) | (n,x) <- xs, v <- vs] $
            eval rhs
        _ -> next
