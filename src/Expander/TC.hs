{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}
module Expander.TC (unify, freshMeta, inst, specialize, varType, makeTypeMetas, generalizeType, normType) where

import Control.Lens hiding (indices)
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Numeric.Natural

import Expander.Monad
import Core
import SplitCore
import Syntax.SrcLoc
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

-- expand outermost constructor to a non-variable, if possible
normType :: Ty -> Expand Ty
normType t@(unTy -> TyF (TMetaVar ptr) args) =
  if null args
  then do
    tv <- derefType ptr
    case view varKind tv of
      Link found -> do
        t' <- normType (Ty found)
        setTVKind ptr (Link (unTy t'))
        return t'
      _ -> return t
  else throwError $ InternalError "type variable cannot have parameters (yet)"
normType t = return t

normAll :: Ty -> Expand Ty
normAll t = do
  Ty (TyF ctor tArgs) <- normType t
  Ty <$> TyF ctor <$> traverse normType tArgs

metas :: Ty -> Expand [MetaPtr]
metas t = do
  Ty (TyF ctor tArgs) <- normType t
  let ctorMetas = case ctor of
                    TMetaVar x -> [x]
                    _ -> []
  argsMetas <- concat <$> traverse metas tArgs
  pure $ ctorMetas ++ argsMetas

occursCheck :: MetaPtr -> Ty -> Expand ()
occursCheck ptr t = do
  free <- metas t
  if ptr `elem` free
    then do
      t' <- normAll t
      throwError $ TypeCheckError $ OccursCheckFailed ptr t'
    else pure ()

pruneLevel :: Traversable f => BindingLevel -> f MetaPtr -> Expand ()
pruneLevel l = traverse_ reduce
  where
    reduce ptr =
      modifyState $
      over (expanderTypeStore . ix ptr . varLevel) (min l)

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
  | otherwise = instTy ty
  where
    instTy :: Ty -> Expand Ty
    instTy t = do
      t' <- normType t
      Ty <$> instTyF (unTy t')

    instTyF :: TyF Ty -> Expand (TyF Ty)
    instTyF (TyF ctor tArgs) = do
      let TyF ctor' tArgsPrefix = instCtor ctor
      tArgsSuffix <- traverse instTy tArgs

      -- If ctor was a TSchemaVar which got instantiated to a partially applied
      -- type constructor such as (TyF TFun [TInteger]), we want to append the remaining
      -- type arguments, e.g. [TSyntax], in order to get (TyF TFun [TInteger, TSyntax]).
      pure $ TyF ctor' (tArgsPrefix ++ tArgsSuffix)

    instCtor :: TypeConstructor -> TyF Ty
    instCtor (TSchemaVar i) = unTy $ ts !! fromIntegral i
    instCtor ctor           = TyF ctor []


specialize :: Scheme Ty -> Expand Ty
specialize sch@(Scheme n _) = do
  freshVars <- makeTypeMetas n
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
      Ty <$> genVarsTyF vars t'

    genVarsTyF ::
      [MetaPtr] -> TyF Ty ->
      StateT (Natural, Map MetaPtr Natural) Expand (TyF Ty)
    genVarsTyF vars (TyF ctor args) =
      TyF <$> genVarsCtor vars ctor
          <*> traverse (genTyVars vars) args

    genVarsCtor ::
      [MetaPtr] -> TypeConstructor ->
      StateT (Natural, Map MetaPtr Natural) Expand TypeConstructor
    genVarsCtor vars (TMetaVar v)
      | v `elem` vars = do
          (i, indices) <- get
          case Map.lookup v indices of
            Nothing -> do
              put (i + 1, Map.insert v i indices)
              pure $ TSchemaVar i
            Just j -> pure $ TSchemaVar j
      | otherwise = pure $ TMetaVar v
    genVarsCtor _ (TSchemaVar _) =
      throwError $ InternalError "Can't generalize in schema"
    genVarsCtor _ ctor =
      pure ctor


makeTypeMetas :: Natural -> Expand [Ty]
makeTypeMetas n = replicateM (fromIntegral n) $ tMetaVar <$> freshMeta

class UnificationErrorBlame a where
  getBlameLoc :: a -> Expand (Maybe SrcLoc)

instance UnificationErrorBlame SrcLoc where
  getBlameLoc = pure . pure

instance UnificationErrorBlame SplitCorePtr where
  getBlameLoc ptr = view (expanderOriginLocations . at ptr) <$> getState

unify :: UnificationErrorBlame blame => blame -> Ty -> Ty -> Expand ()
unify loc t1 t2 = unifyWithBlame (loc, t1, t2) 0 t1 t2

-- The expected type is first, the received is second
unifyWithBlame :: UnificationErrorBlame blame => (blame, Ty, Ty) -> Natural -> Ty -> Ty -> Expand ()
unifyWithBlame blame depth t1 t2 = do
  t1' <- normType t1
  t2' <- normType t2
  unifyTyFs (unTy t1') (unTy t2')

  where
    unifyTyFs :: TyF Ty -> TyF Ty -> Expand ()

    -- Flex-flex
    unifyTyFs (TyF (TMetaVar ptr1) args1) (TyF (TMetaVar ptr2) args2) =
      if null args1 && null args2
      then do
        l1 <- view varLevel <$> derefType ptr1
        l2 <- view varLevel <$> derefType ptr2
        if | ptr1 == ptr2 -> pure ()
           | l1 < l2 -> linkToType ptr1 t2
           | otherwise -> linkToType ptr2 t1
      else throwError $ InternalError "type variable cannot have parameters (yet)"

    -- Flex-rigid
    unifyTyFs (TyF (TMetaVar ptr1) args1) _ =
      if null args1
      then linkToType ptr1 t2
      else throwError $ InternalError "type variable cannot have parameters (yet)"
    unifyTyFs _ (TyF (TMetaVar ptr2) args2) =
      if null args2
      then linkToType ptr2 t1
      else throwError $ InternalError "type variable cannot have parameters (yet)"

    unifyTyFs expected@(TyF ctor1 args1) received@(TyF ctor2 args2) =
      if ctor1 == ctor2 && length args1 == length args2
      then do
        -- Rigid-rigid
        for_ (zip args1 args2) $ \(arg1, arg2) -> do
          unifyWithBlame blame (depth + 1) arg1 arg2
      else do
        -- Mismatch
        let (here, outerExpected, outerReceived) = blame
        loc <- getBlameLoc here
        e' <- normAll $ Ty expected
        r' <- normAll $ Ty received
        if depth == 0
          then throwError $ TypeCheckError $ TypeMismatch loc e' r' Nothing
          else do
            outerE' <- normAll outerExpected
            outerR' <- normAll outerReceived
            throwError $ TypeCheckError $ TypeMismatch loc outerE' outerR' (Just (e', r'))
