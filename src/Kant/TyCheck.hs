{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.TyCheck
    ( TyCheckError(..)
    , expectingTypeData
    , wrongRecTypePos
    , MonadTyCheck
    , tyInfer
    , tyInferNH
    ) where

import           Control.Applicative (Applicative, (<$>), (<$), (<*>))
import           Control.Monad (unless)

import           Control.Monad.Error (MonadError(..), Error, ErrorT)
import           Control.Monad.State (StateT(..), MonadState(..))

import           Bound

import           Kant.Env
import           Kant.Reduce
import           Kant.Term
import           Kant.Constraint
import           Kant.Uniquify

data TyCheckError
    = OutOfBounds Id
    | DuplicateName Id
    | Mismatch TermRefId TermRefId TermRefId
    | ExpectingFunction TermRefId TermRefId
    | ExpectingType TermRefId TermRefId
    | ExpectingTypeCon ConId TermRefId
    | ExpectingTypeData ConId ConId TermRefId
    | WrongRecTypePos ConId ConId TermRefId
    | UntypedTerm TermRefId
    | UnexpectedHole HoleId
    | CyclicTypes               -- TODO more descriptive
    deriving (Eq, Show)

instance Error TyCheckError

class (Functor m, Applicative m, MonadError TyCheckError m) => MonadTyCheck m
instance MonadTyCheck (ErrorT TyCheckError IO)
instance (MonadTyCheck m) => MonadTyCheck (StateT s m)

mismatch :: (VarC v, MonadTyCheck m)
         => Env v -> TermRef v -> TermRef v -> TermRef v -> m a
mismatch env t₁ t₂ t₃ =
    runFresh $ do [t₁', t₂', t₃'] <- mapM (slam env) [t₁, t₂, t₃]
                  return (throwError (Mismatch t₁' t₂' t₃'))

expectingType :: (VarC v, MonadTyCheck m) => Env v -> TermRef v -> TermRef v -> m a
expectingType env t ty =
    runFresh $ do [t', ty'] <- mapM (slam env) [t, ty]
                  return (throwError (ExpectingType t' ty'))

expectingFunction :: (VarC v, MonadTyCheck m)
                  => Env v -> TermRef v -> TermRef v -> m a
expectingFunction env t ty =
    runFresh $ do [t', ty'] <- mapM (slam env) [t, ty]
                  return (throwError (ExpectingFunction t' ty'))

expectingTypeData :: (VarC v, MonadTyCheck m)
                  => Env v -> ConId -> ConId -> TermRef v -> m a
expectingTypeData env dc tyc ty  =
    throwError (ExpectingTypeData dc tyc (slam' env ty))

wrongRecTypePos :: (VarC v, MonadTyCheck m)
                => Env v -> ConId -> ConId -> TermRef v -> m a
wrongRecTypePos env dc tyc ty =
    throwError (WrongRecTypePos dc tyc (slam' env ty))

untypedTerm :: (VarC v, MonadError TyCheckError m)
            => Env v -> TermRef v -> m a
untypedTerm env t = throwError (UntypedTerm (slam' env t))

lookupTy :: (VarC v, MonadTyCheck m) => Env v -> v -> m (TermRef v)
lookupTy env v = case envType env v of
                     Nothing -> throwError (OutOfBounds (envPull env v))
                     Just ty -> return ty

type TyMonad m = StateT ([HoleCtx], Ref, ConstrsRef) m

addHole :: Monad m => HoleCtx -> TyMonad m ()
addHole hole = do (holes, r, constrs) <- get; put (hole : holes, r, constrs)

freshRef :: MonadTyCheck m => TyMonad m Ref
freshRef = do (holes, r, constrs) <- get; r <$ put (holes, r + 1, constrs)

newConstrs :: MonadTyCheck m => [ConstrRef] -> TyMonad m ()
newConstrs cs =
    do (holes, r, constrs) <- get
       constrs' <- maybe (throwError CyclicTypes) return (addConstrs cs constrs)
       put (holes, r, constrs')

newConstrs' :: MonadTyCheck m => (Ref -> [ConstrRef]) -> TyMonad m Ref
newConstrs' f = do r <- freshRef
                   newConstrs (f r)
                   return r

newConstr' :: MonadTyCheck m => (Ref -> ConstrRef) -> TyMonad m Ref
newConstr' f = newConstrs' (return . f)

tyInfer :: (VarC v, MonadTyCheck m)
        => Env v -> TermRef v -> m (TermRef v, [HoleCtx], Env v)
tyInfer env t =
    do (ty, (holes, r, constrs)) <-
           runStateT (tyInfer' env t) ([], envRef env, envConstrs env)
       return (ty, reverse holes, env{envRef = r, envConstrs = constrs})

-- TODO this should be never necessary, I should allow holes in data decls
tyInferNH :: (VarC v, MonadTyCheck m) => Env v -> TermRef v -> m (TermRef v, Env v)
tyInferNH env t =
    do (ty, holes, env') <- tyInfer env t
       case holes of
           []                           -> return (ty, env')
           (HoleCtx{holeName = hn} : _) -> throwError (UnexpectedHole hn)

tyInfer' :: (VarC v, MonadTyCheck m) => Env v -> TermRef v -> TyMonad m (TermRef v)
tyInfer' _ (Ty r) = Ty <$> newConstr' (r :<:)
tyInfer' env (V v) = lookupTy env v
tyInfer' env t@(Lam _) = untypedTerm env t
tyInfer' env₁ (Arr ty₁ s) =
    do tyty₁ <- tyInfer' env₁ ty₁
       case whnf env₁ tyty₁ of
           (Ty r₁) -> do let env₂ = nestEnvTy env₁ ty₁
                             ty₂ = fromScope s
                         tyty₂ <- tyInfer' env₂ ty₂
                         case nf env₂ tyty₂ of
                             (Ty r₂) -> Ty <$>
                                        newConstrs' (\r -> [r₁ :<=: r, r₂ :<=: r])
                             _       -> expectingType env₂ ty₂ tyty₂
           _ -> expectingType env₁ ty₁ tyty₁
tyInfer' env (App t₁ t₂) =
    do tyt₁ <- tyInfer' env t₁
       case whnf env tyt₁ of
           Arr ty₁ s -> do tyCheck env t₂ ty₁; return (instantiate1 t₂ s)
           _         -> expectingFunction env t₁ tyt₁
tyInfer' env (Canon dc ts) = tyInfer' env (app (V (envNest env dc) : ts))
tyInfer' env (Elim en ts) = tyInfer' env (app (V (envNest env en) : ts))
tyInfer' env (Ann ty t) =
    -- TODO we can avoid the fresh ref here
    do tyCheck env ty . Ty =<< freshRef
       ty <$ tyCheck env t ty
tyInfer' env t@(Hole _ _) = untypedTerm env t

tyCheck :: (VarC v, MonadTyCheck m) => Env v -> TermRef v -> TermRef v -> TyMonad m ()
tyCheck env₀ t₀ ty₀ = go env₀ t₀ (nf env₀ ty₀)
  where
    go :: (VarC v, MonadTyCheck m) => Env v -> TermRef v -> TermRef v -> TyMonad m ()
    go env (Lam s₁) (Arr ty s₂) =
        go (nestEnvTy env ty) (fromScope s₁) (fromScope s₂)
    go env (Hole hn ts) ty =
        do tys <- mapM (tyInfer' env) ts
           addHole (runFresh (formHole env hn ty (zip ts tys)))
    go env t ty =
        do tyt <- nf env <$> tyInfer' env t
           eq <- eqRefs ty tyt
           unless eq (mismatch env ty t tyt)

-- TODO maybe find a way to eliminate the explicit recursion?
eqRefs :: (VarC v, MonadTyCheck m) => TermRef v -> TermRef v -> TyMonad m Bool
eqRefs (V v₁) (V v₂) = return (v₁ == v₂)
eqRefs (Ty r₁) (Ty r₂) = do newConstrs [r₁ :==: r₂]; return True
eqRefs (Lam s₁) (Lam s₂) = eqRefs (fromScope s₁) (fromScope s₂)
eqRefs (Arr ty₁ s₁) (Arr ty₂ s₂) =
    (&&) <$> eqRefs ty₁ ty₂ <*> eqRefs (fromScope s₁) (fromScope s₂)
eqRefs (App t₁ t'₁) (App t₂ t'₂) = (&&) <$> eqRefs t₁ t₂ <*> eqRefs t'₁ t'₂
eqRefs (Ann ty₁ t₁) (Ann ty₂ t₂) = (&&) <$> eqRefs ty₁ ty₂ <*> eqRefs t₁ t₂
eqRefs (Canon c₁ ts₁) (Canon c₂ ts₂) =
    ((c₁ == c₂ &&) . and) <$> mapM (uncurry eqRefs) (zip ts₁ ts₂)
eqRefs (Elim c₁ ts₁) (Elim c₂ ts₂) =
    ((c₁ == c₂ &&) . and) <$> mapM (uncurry eqRefs) (zip ts₁ ts₂)
eqRefs (Hole x _) (Hole y _) = return (x == y)
eqRefs _ _ = return False
