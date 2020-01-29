{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
module Expander.TC where

import Control.Lens
import Control.Monad.Except
import Data.Foldable

import Expander.Monad
import Core
import Type


derefType :: MetaPtr -> Expand (TVar Ty)
derefType ptr =
  (view (expanderTypeStore . at ptr) <$> getState) >>=
  \case
    Nothing -> throwError $ InternalError "Dangling type metavar"
    Just var -> pure var


setTVKind :: MetaPtr -> VarKind Ty -> Expand ()
setTVKind ptr k = do
  _ <- derefType ptr -- fail if not present
  modifyState $ over (expanderTypeStore . at ptr) $ fmap (set varKind k)

setTVLevel :: MetaPtr -> BindingLevel -> Expand ()
setTVLevel ptr l = do
  _ <- derefType ptr -- fail if not present
  modifyState $ over (expanderTypeStore . at ptr) $ fmap (set varLevel l)

normType :: Ty -> Expand Ty
normType t@(unTy -> TMetaVar ptr) = do
  tv <- derefType ptr
  case view varKind tv of
    Link found -> do
      t' <- normType (Ty found)
      setTVKind ptr (Link (unTy t'))
      return t'
    _ -> return t
normType t = return t

metas :: Ty -> Expand [MetaPtr]
metas t =
  normType t >>=
  \case
    Ty (TMetaVar x) -> pure [x]
    Ty (TFun a b) -> (++) <$> metas a <*> metas b
    Ty (TMacro a) -> metas a
    Ty (TList a) -> metas a
    _ -> pure []

occursCheck :: MetaPtr -> Ty -> Expand ()
occursCheck ptr t = do
  free <- metas t
  if ptr `elem` free
    then throwError $ OccursCheckFailed
    else pure ()

pruneLevel :: Traversable f => BindingLevel -> f MetaPtr -> Expand ()
pruneLevel l = traverse_ reduce
  where
    reduce ptr =
      modifyState $
      over (expanderTypeStore . at ptr) $
      fmap (over varLevel (min l))

linkToType :: MetaPtr -> Ty -> Expand ()
linkToType var ty = do
  lvl <- view varLevel <$> derefType var
  occursCheck var ty
  pruneLevel lvl =<< metas ty
  setTVKind var (Link (unTy ty))

freshMeta :: Expand MetaPtr
freshMeta = do
  lvl <- currentBindingLevel
  ptr <- liftIO $ newMetaPtr
  modifyState (set (expanderTypeStore . at ptr) (Just (TVar NoLink lvl)))
  return ptr

inst :: Scheme Ty -> [Ty] -> Expand Ty
inst (Scheme n ty) ts
  | length ts /= fromIntegral n = throwError $ InternalError "Mismatch in number of type vars"
  | otherwise = instNorm ty
  where
    instNorm t = do
      t' <- normType t
      Ty <$> inst' (unTy t')

    inst' (TFun a b) = TFun <$> instNorm a <*> instNorm b
    inst' (TMacro a) = TMacro <$> instNorm a
    inst' (TList a) = TList <$> instNorm a
    inst' (TSchemaVar i) = pure . unTy $ ts !! fromIntegral i
    inst' otherTy = pure otherTy


specialize :: Scheme Ty -> Expand Ty
specialize sch@(Scheme n _) = do
  freshVars <- replicateM (fromIntegral n) $ Ty . TMetaVar <$> freshMeta
  inst sch freshVars

varType :: Var -> Expand (Scheme Ty)
varType x = do
  ph <- currentPhase
  now <- view (expanderLocal . expanderVarTypes . at ph)
  let γ = case now of
            Nothing -> mempty
            Just γ' -> γ'
  case view (at x) γ of
    Nothing -> error "TODO error message"
    Just (_, ty) -> pure ty
