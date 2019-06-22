module Evaluator where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Unique
import qualified Data.Map as Map

import Syntax
import Core
import Value


data Error
  = ErrorSyntax SyntaxError
  | ErrorUnbound Var

type Eval = ReaderT Env (ExceptT Error IO)

eval :: Core -> Eval Value
eval (CoreVar var) = do
  env <- ask
  case Map.lookup var env of
    Just (ident, value) -> pure value
    _ -> throwError $ ErrorUnbound var
eval (CoreLam ident var body) = do
  env <- ask
  pure $ ValueClosure $ Closure
    { closureEnv   = env
    , closureIdent = ident
    , closureVar   = var
    , closureBody  = body
    }
eval (CoreApp fun arg) = undefined
eval (CoreSyntaxError syntaxError) = undefined
eval (CoreSyntax syntax) = undefined
eval (CoreCase scrutinee cases) = undefined
eval (CoreIdentifier ident) = undefined
eval (CoreIdent scopedIdent) = undefined
eval (CoreEmpty scopedEmpty) = undefined
eval (CoreCons scopedCons) = undefined
eval (CoreVec scopedVec) = undefined
