{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wno-unused-top-binds #-}  -- setTVLevel is currently unused
module Expander.TC (
  -- * Type checking
  unify, freshMeta, inst, specialize, varType, makeTypeMeta, generalizeType, normType,
  -- * Kind checking
  equateKinds, typeVarKind
  ) where

import Control.Lens hiding (indices)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable
import Data.Traversable (for)
import Numeric.Natural

import Expander.Monad
import Core
import Datatype
import Kind
import SplitCore
import Syntax (Syntax, stxLoc)
import Syntax.SrcLoc
import Type
import World

import Util.Store (Store)
import qualified Util.Store as St

derefType :: MetaPtr -> Expand (TVar Ty)
derefType ptr =
  (view (expanderTypeStore . at ptr) <$> getState) >>=
  \case
    Nothing -> throwError $ InternalError "Dangling type metavar"
    Just var -> pure var


setTVLinkage :: MetaPtr -> VarLinkage Ty -> Expand ()
setTVLinkage ptr k = do
  _ <- derefType ptr -- fail if not present
  modifyState $ over (expanderTypeStore . at ptr) $ fmap (set varLinkage k)

setTVLevel :: MetaPtr -> BindingLevel -> Expand ()
setTVLevel ptr l = do
  _ <- derefType ptr -- fail if not present
  modifyState $ over (expanderTypeStore . at ptr) $ fmap (set varLevel l)

-- expand outermost constructor to a non-variable, if possible
normType :: Ty -> Expand Ty
normType t@(unTy -> TyF (TMetaVar ptr) args) = do
  tv <- derefType ptr
  case view varLinkage tv of
    Link found -> do
      t'@(Ty (TyF ctor tyArgs)) <- normType (Ty found)
      setTVLinkage ptr (Link (unTy t'))
      return $ Ty (TyF ctor (tyArgs <> args))
    _ -> return t
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

linkToType :: UnificationErrorBlame blame => blame -> MetaPtr -> Ty -> Expand ()
linkToType blame var ty = do
  lvl <- view varLevel <$> derefType var
  occursCheck var ty
  pruneLevel lvl =<< metas ty
  k <- typeVarKind var
  checkKind blame k ty
  setTVLinkage var (Link (unTy ty))

freshMeta :: Maybe Kind -> Expand MetaPtr
freshMeta kind = do
  lvl <- currentBindingLevel
  ptr <- liftIO newMetaPtr
  k <- maybe (KMetaVar <$> liftIO newKindVar) pure kind
  modifyState (set (expanderTypeStore . at ptr) (Just (TVar NoLink lvl k)))
  return ptr


inst :: UnificationErrorBlame blame => blame -> Scheme Ty -> Store SchemeVar Ty -> Expand Ty
inst blame (Scheme argKinds ty) ts
  | length ts /= length argKinds =
    throwError $ InternalError "Mismatch in number of type vars"
  | otherwise = do
      let tys :: [Ty]
          tys = fmap snd $ St.toAscList ts
      traverse_ (uncurry $ checkKind blame) (zip argKinds tys)
      instTy ty
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
    instCtor (TSchemaVar v) = unTy $ ts St.! v
    instCtor ctor           = TyF ctor []


specialize :: UnificationErrorBlame blame => blame -> Scheme Ty -> Expand Ty
specialize blame sch@(Scheme argKinds _) = do
  pairs <- for (zip [firstSchemeVar..] argKinds) $ \(v, k) -> do
    meta <- makeTypeMeta k
    pure (v, meta)
  let freshVars :: Store SchemeVar Ty
      freshVars = St.fromList pairs
  inst blame sch freshVars

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
  (body, (_, _, argKinds)) <- flip runStateT (firstSchemeVar, mempty, []) $ do
    genTyVars canGeneralize ty
  pure $ Scheme argKinds body

  where
    genTyVars ::
      [MetaPtr] -> Ty ->
      StateT (SchemeVar, Store MetaPtr SchemeVar, [Kind]) Expand Ty
    genTyVars vars t = do
      (Ty t') <- lift $ normType t
      Ty <$> genVarsTyF vars t'

    genVarsTyF ::
      [MetaPtr] -> TyF Ty ->
      StateT (SchemeVar, Store MetaPtr SchemeVar, [Kind]) Expand (TyF Ty)
    genVarsTyF vars (TyF ctor args) =
      TyF <$> genVarsCtor vars ctor
          <*> traverse (genTyVars vars) args

    genVarsCtor ::
      [MetaPtr] -> TypeConstructor ->
      StateT (SchemeVar, Store MetaPtr SchemeVar, [Kind]) Expand TypeConstructor
    genVarsCtor vars (TMetaVar v)
      | v `elem` vars = do
          (i, indices, argKinds) <- get
          case St.lookup v indices of
            Nothing -> do
              k <- lift $ typeVarKind v
              put (succ i, St.insert v i indices, argKinds ++ [k])
              pure $ TSchemaVar i
            Just j -> pure $ TSchemaVar j
      | otherwise = pure $ TMetaVar v
    genVarsCtor _ (TSchemaVar _) =
      throwError $ InternalError "Can't generalize in scheme"
    genVarsCtor _ ctor =
      pure ctor


makeTypeMeta :: Kind -> Expand Ty
makeTypeMeta k = tMetaVar <$> freshMeta (Just k)

class UnificationErrorBlame a where
  getBlameLoc :: a -> Expand (Maybe SrcLoc)

instance UnificationErrorBlame SrcLoc where
  getBlameLoc = pure . pure

instance UnificationErrorBlame Syntax where
  getBlameLoc = pure . pure . stxLoc

instance UnificationErrorBlame SplitCorePtr where
  getBlameLoc ptr = view (expanderOriginLocations . at ptr) <$> getState

unify :: UnificationErrorBlame blame => blame -> Ty -> Ty -> Expand ()
unify loc t1 t2 = do
  -- NB is this kind check necessary?
  k1 <- inferKind loc t1
  checkKind loc k1 t2
  unifyWithBlame (loc, t1, t2) 0 t1 t2

-- The expected type is first, the received is second
unifyWithBlame :: UnificationErrorBlame blame => (blame, Ty, Ty) -> Natural -> Ty -> Ty -> Expand ()
unifyWithBlame blame depth t1 t2 = do
  t1' <- normType t1
  t2' <- normType t2
  unifyTyFs (unTy t1') (unTy t2')

  where
    unifyTyFs :: TyF Ty -> TyF Ty -> Expand ()

    -- Flex-flex
    unifyTyFs (TyF (TMetaVar ptr1) args1) (TyF (TMetaVar ptr2) args2)
      | length args1 == length args2 = do
        l1 <- view varLevel <$> derefType ptr1
        l2 <- view varLevel <$> derefType ptr2
        if | ptr1 == ptr2 -> pure ()
           | l1 < l2 -> linkVar ptr1 t2
           | otherwise -> linkVar ptr2 t1
        traverse_ (uncurry $ unifyWithBlame blame (depth + 1)) (zip args1 args2)
      | null args1 = linkVar ptr1 t2
      | null args2 = linkVar ptr2 t1
      | otherwise = do
          let argCount1 = length args1
          let argCount2 = length args2
          let argCount = min argCount1 argCount2
          let args1' = drop (argCount1 - argCount) args1
          let args2' = drop (argCount2 - argCount) args2
          traverse_ (uncurry $ unifyWithBlame blame (depth + 1)) (zip args1' args2')
          unifyWithBlame blame (depth + 1)
            (Ty (TyF (TMetaVar ptr1) (take (argCount1 - argCount) args1)))
            (Ty (TyF (TMetaVar ptr2) (take (argCount2 - argCount) args2)))

    -- Flex-rigid
    unifyTyFs shouldBe@(TyF (TMetaVar ptr1) args1) received@(TyF ctor2 args2)
      | null args1 =
        linkVar ptr1 t2
      | length args1 <= length args2 = do
          traverse_ (uncurry $ unifyWithBlame blame (depth + 1)) $
            zip args1 (drop (length args2 - length args1) args2)
          let args2' = take (length args2 - length args1) args2
          unifyWithBlame blame (depth + 1) (Ty $ TyF (TMetaVar ptr1) []) (Ty $ TyF ctor2 args2')
      | otherwise = mismatch shouldBe received

    unifyTyFs shouldBe@(TyF ctor1 args1) received@(TyF (TMetaVar ptr2) args2)
      | null args2 = do
          linkVar ptr2 t1
      | length args2 <= length args1 = do
          traverse_ (uncurry $ unifyWithBlame blame (depth + 1)) $
            zip (drop (length args1 - length args2) args1) args2
          let args1' = take (length args1 - length args2) args1
          unifyWithBlame blame (depth + 1) (Ty $ TyF ctor1 args1') (Ty $ TyF (TMetaVar ptr2) [])
      | otherwise = mismatch shouldBe received


    unifyTyFs shouldBe@(TyF ctor1 args1) received@(TyF ctor2 args2)
      -- Rigid-rigid
      | ctor1 == ctor2 && length args1 == length args2 =
          for_ (zip args1 args2) $ \(arg1, arg2) ->
            unifyWithBlame blame (depth + 1) arg1 arg2
      | otherwise = mismatch shouldBe received

    mismatch shouldBe received = do
        let (here, outerExpected, outerReceived) = blame
        loc <- getBlameLoc here
        e' <- normAll $ Ty shouldBe
        r' <- normAll $ Ty received
        if depth == 0
          then throwError $ TypeCheckError $ TypeMismatch loc e' r' Nothing
          else do
            outerE' <- normAll outerExpected
            outerR' <- normAll outerReceived
            throwError $ TypeCheckError $ TypeMismatch loc outerE' outerR' (Just (e', r'))

    linkVar ptr t = linkToType (view _1 blame) ptr t


typeVarKind :: MetaPtr -> Expand Kind
typeVarKind ptr =
  (view (expanderTypeStore . at ptr) <$> getState) >>=
  \case
    Nothing -> throwError $ InternalError "Type variable not found!"
    Just v -> pure $ view varKind v


kindMetas :: Kind -> Expand [KindVar]
kindMetas k = do
  k' <- zonkKind k
  case k' of
    KMetaVar v' ->
      (view (expanderKindStore . at v') <$> getState) >>=
      \case
        Nothing -> pure [v']
        Just k'' -> kindMetas k''
    KStar -> pure []
    KFun k1 k2 -> (++) <$> kindMetas k1 <*> kindMetas k2


-- pre-condition: 'v' zonks to itself.
-- post-condition: 'k' zonks to a kind which does not contain 'v'.
kindOccursCheck :: KindVar -> Kind -> Expand ()
kindOccursCheck v k = do
  free <- kindMetas k
  if v `elem` free
    then do
      k' <- zonkKind k
      throwError $ KindCheckError $ KindOccursCheckFailed v k'
    else pure ()

-- pre-condition: 'v' zonks to itself.
-- post-condition: @KMetaVar v@, 'k', and the return value all zonk to the same
-- kind.
setKindVar :: KindVar -> Kind -> Expand Kind
setKindVar v k@(KMetaVar v')
  | v == v' =
      pure k
  | otherwise =
      (view (expanderKindStore . at v') <$> getState) >>=
      \case
        Nothing -> do
          kindOccursCheck v k
          modifyState $ set (expanderKindStore . at v) (Just k)
          pure k
        Just k' -> do
          -- Recur to the root, both to compress the path from 'v' and to
          -- make sure we don't make 'v' point indirectly to itself.
          k'' <- setKindVar v k'
          -- Also compress v'
          modifyState $ set (expanderKindStore . at v') (Just k'')
          pure k''
setKindVar v k = do
  kindOccursCheck v k
  modifyState $ set (expanderKindStore . at v) (Just k)
  pure k

-- post-condition: 'kind1' and 'kind2' both zonk to the same kind.
equateKinds :: UnificationErrorBlame blame => blame -> Kind -> Kind -> Expand ()
equateKinds blame kind1 kind2 =
  equateKinds' kind1 kind2 >>=
  \case
    True -> pure ()
    False -> do
      k1' <- zonkKind kind1
      k2' <- zonkKind kind2
      loc <- getBlameLoc blame
      throwError $ KindCheckError $ KindMismatch loc k1' k2'
  where
    -- Rigid-rigid cases
    equateKinds' KStar KStar = pure True
    equateKinds' (KFun k1 k2) (KFun k1' k2') =
      (&&) <$> equateKinds' k1 k1' <*> equateKinds' k2 k2'
    -- Flex-flex
    equateKinds' (KMetaVar v1) (KMetaVar v2)
      | v1 == v2 = pure True
      | otherwise = do
          k1 <- view (expanderKindStore . at v1) <$> getState
          k2 <- view (expanderKindStore . at v2) <$> getState
          case (k1, k2) of
            (Nothing, Nothing) -> setKindVar v1 (KMetaVar v2) >> pure True
            (Just k, Nothing) ->  setKindVar v2 k >> pure True
            (Nothing, Just k) ->  setKindVar v1 k >> pure True
            (Just k, Just k') ->  equateKinds' k k'
    -- Flex-rigid
    equateKinds' (KMetaVar v) k =
      (view (expanderKindStore . at v) <$> getState) >>=
      \case
        Just k' -> equateKinds' k' k
        Nothing -> setKindVar v k >> pure True
    equateKinds' k (KMetaVar v) =
      (view (expanderKindStore . at v) <$> getState) >>=
      \case
        Just k' -> equateKinds' k k'
        Nothing -> setKindVar v k >> pure True
    -- Errors
    equateKinds' _ _ = pure False

checkKind :: UnificationErrorBlame blame => blame -> Kind -> Ty -> Expand ()
checkKind blame k t = do
  k' <- inferKind blame t
  equateKinds blame k k'

inferKind :: UnificationErrorBlame blame => blame -> Ty -> Expand Kind
inferKind blame (Ty (TyF ctor args)) = do
  k1 <- ctorKind ctor
  argKinds <- traverse (inferKind blame) args
  appKind k1 argKinds

  where
    ctorKind TSyntax = pure KStar
    ctorKind TInteger = pure KStar
    ctorKind TString = pure KStar
    ctorKind TOutputPort = pure KStar
    ctorKind TFun = pure $ kFun [KStar, KStar] KStar
    ctorKind TMacro = pure $ kFun [KStar] KStar
    ctorKind TIO = pure $ kFun [KStar] KStar
    ctorKind TType = pure KStar
    ctorKind (TDatatype dt) = do
      DatatypeInfo argKinds _ <- datatypeInfo dt
      pure $ kFun argKinds KStar
    ctorKind (TSchemaVar _) = throwError $ InternalError "Tried to find kind in open context"
    ctorKind (TMetaVar mv) = typeVarKind mv

    appKind k [] = pure k
    appKind (KFun k1 k2) (k : ks) =
      equateKinds blame k1 k *> appKind k2 ks
    appKind other (k : ks) = do
      k1 <- KMetaVar <$> liftIO newKindVar
      k2 <- KMetaVar <$> liftIO newKindVar
      equateKinds blame other (KFun k1 k2)
      appKind (KFun k1 k2) (k : ks)
