{-# LANGUAGE GeneralizedNewtypeDeriving, RecordWildCards #-}
module Evaluator where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Unique
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

newtype Eval a = Eval
   { runEval :: ReaderT Env (ExceptT Error IO) a }
   deriving (Functor, Applicative, Monad, MonadReader Env, MonadError Error)

withEnv :: Env -> Eval a -> Eval a
withEnv = local . const

eval :: Core -> Eval Value
eval (CoreVar var) = do
  env <- ask
  case Map.lookup var env of
    Just (_ident, value) -> pure value
    _ -> throwError $ ErrorUnbound var
eval (CoreLam ident var body) = do
  env <- ask
  pure $ ValueClosure $ Closure
    { closureEnv   = env
    , closureIdent = ident
    , closureVar   = var
    , closureBody  = body
    }
eval (CoreApp fun arg) = do
  funValue <- eval fun
  argValue <- eval arg
  case funValue of
    ValueClosure (Closure {..}) -> do
      let env = Map.insert closureVar
                           (closureIdent, argValue)
                           closureEnv
      withEnv env $ do
        eval closureBody
    ValueSyntax syntax -> do
      throwError $ ErrorType $ TypeError
        { typeErrorExpected = "function"
        , typeErrorActual   = "syntax"
        }
eval (CoreSyntaxError syntaxError) = do
  throwError $ ErrorSyntax syntaxError
eval (CoreSyntax syntax) = do
  pure $ ValueSyntax syntax
eval (CoreCase scrutinee cases) = undefined
eval (CoreIdentifier ident) = undefined
eval (CoreIdent scopedIdent) = undefined
eval (CoreEmpty scopedEmpty) = undefined
eval (CoreCons scopedCons) = undefined
eval (CoreVec scopedVec) = undefined
