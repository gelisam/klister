{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
module Expander.TC where

import Control.Lens hiding (indices)
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Numeric.Natural

import Expander.Monad
import Core
import Type
import World

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

normAll :: Ty -> Expand Ty
normAll t =
  normType t >>= fmap Ty .
  \case
    (Ty (TFun a b)) -> TFun <$> normType a <*> normType b
    (Ty (TMacro a)) -> TMacro <$> normType a
    (Ty (TDatatype dt tArgs)) ->
      TDatatype dt <$> traverse normType tArgs
    other -> pure (unTy other)

metas :: Ty -> Expand [MetaPtr]
metas t =
  normType t >>=
  \case
    Ty (TMetaVar x) -> pure [x]
    Ty (TFun a b) -> (++) <$> metas a <*> metas b
    Ty (TMacro a) -> metas a
    Ty (TDatatype _ ts) -> concat <$> traverse metas ts
    _ -> pure []

occursCheck :: MetaPtr -> Ty -> Expand ()
occursCheck ptr t = do
  free <- metas t
  if ptr `elem` free
    then do
      t' <- normAll t
      throwError $ OccursCheckFailed ptr t'
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
  | length ts /= fromIntegral n =
    throwError $ InternalError "Mismatch in number of type vars"
  | otherwise = instNorm ty
  where
    instNorm t = do
      t' <- normType t
      Ty <$> inst' (unTy t')

    inst' (TFun a b) = TFun <$> instNorm a <*> instNorm b
    inst' (TMacro a) = TMacro <$> instNorm a
    inst' (TDatatype dt ts) = TDatatype dt <$> traverse instNorm ts
    inst' (TSchemaVar i) = pure . unTy $ ts !! fromIntegral i
    inst' otherTy = pure otherTy


specialize :: Scheme Ty -> Expand Ty
specialize sch@(Scheme n _) = do
  freshVars <- replicateM (fromIntegral n) $ Ty . TMetaVar <$> freshMeta
  inst sch freshVars

varType :: Var -> Expand (Maybe (Scheme Ty))
varType x = do
  ph <- currentPhase
  globals <- view (expanderWorld . worldTypeContexts) <$> getState
  thisMod <- view expanderDefTypes <$> getState
  locals <- view (expanderLocal . expanderVarTypes)
  let now = view (at ph) (globals <> thisMod <> locals)
  let γ = case now of
            Nothing -> mempty
            Just γ' -> γ'
  case view (at x) γ of
    Nothing -> pure Nothing
    Just (_, ptr) -> linkedScheme ptr

notFreeInCtx :: MetaPtr -> Expand Bool
notFreeInCtx var = do
  lvl <- currentBindingLevel
  (> lvl) . view varLevel <$> derefType var

generalizeType :: Ty -> Expand (Scheme Ty)
generalizeType ty = do
  canGeneralize <- filterM notFreeInCtx =<< metas ty
  (body, (n, _)) <- flip runStateT (0, Map.empty) $
    genTyVars canGeneralize ty
  pure $ Scheme n body

  where
    genTyVars ::
      [MetaPtr] -> Ty ->
      StateT (Natural, Map MetaPtr Natural) Expand Ty
    genTyVars vars t = do
      (Ty t') <- lift $ normType t
      Ty <$> genVars vars t'

    genVars ::
      [MetaPtr] -> TyF Ty ->
      StateT (Natural, Map MetaPtr Natural) Expand (TyF Ty)
    genVars _ TUnit = pure TUnit
    genVars _ TBool = pure TBool
    genVars _ TSyntax = pure TSyntax
    genVars _ TSignal = pure TSignal
    genVars vars (TFun dom ran) =
      TFun <$> genTyVars vars dom <*> genTyVars vars ran
    genVars vars (TMacro a) = TMacro <$> genTyVars vars a
    genVars vars (TDatatype d args) =
      TDatatype d <$> traverse (genTyVars vars) args
    genVars _ (TSchemaVar _) =
      throwError $ InternalError "Can't generalize in schema"
    genVars vars (TMetaVar v)
      | v `elem` vars = do
          (i, indices) <- get
          case Map.lookup v indices of
            Nothing -> do
              put (i + 1, Map.insert v i indices)
              pure $ TSchemaVar i
            Just j -> pure $ TSchemaVar j
      | otherwise = pure $ TMetaVar v
