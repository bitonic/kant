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

import           Control.Applicative (Applicative, (<$>), (<$))
import           Control.Monad (unless)
import           Data.Monoid (Monoid)

import           Control.Monad.Error (MonadError(..), Error, ErrorT)
import           Control.Monad.Writer (MonadWriter(..), WriterT(..))

import           Bound

import           Kant.Env
import           Kant.Reduce
import           Kant.Term
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
    deriving (Eq, Show)

instance Error TyCheckError

class (Functor m, Applicative m, MonadError TyCheckError m) => MonadTyCheck m
instance MonadTyCheck (ErrorT TyCheckError IO)
instance (Monoid w, MonadTyCheck m) => MonadTyCheck (WriterT w m)

mismatch :: (Ord v, Show v, MonadTyCheck m)
         => Env v -> TermRef v -> TermRef v -> TermRef v -> m a
mismatch env t₁ t₂ t₃ =
    runFresh $ do [t₁', t₂', t₃'] <- mapM (slam env) [t₁, t₂, t₃]
                  return (throwError (Mismatch t₁' t₂' t₃'))

expectingType :: (Ord v, Show v, MonadTyCheck m)
              => Env v -> TermRef v -> TermRef v -> m a
expectingType env t ty =
    runFresh $ do [t', ty'] <- mapM (slam env) [t, ty]
                  return (throwError (ExpectingType t' ty'))

expectingFunction :: (Ord v, Show v, MonadTyCheck m)
                  => Env v -> TermRef v -> TermRef v -> m a
expectingFunction env t ty =
    runFresh $ do [t', ty'] <- mapM (slam env) [t, ty]
                  return (throwError (ExpectingFunction t' ty'))

expectingTypeData :: (Ord v, MonadTyCheck m, Show v)
                  => Env v -> ConId -> ConId -> TermRef v -> m a
expectingTypeData env dc tyc ty  =
    throwError (ExpectingTypeData dc tyc (slam' env ty))

wrongRecTypePos :: (Ord v, Show v, MonadTyCheck m)
                => Env v -> ConId -> ConId -> TermRef v -> m a
wrongRecTypePos env dc tyc ty =
    throwError (WrongRecTypePos dc tyc (slam' env ty))

untypedTerm :: (Ord v, Show v, MonadError TyCheckError m)
            => Env v -> TermRef v -> m a
untypedTerm env t = throwError (UntypedTerm (slam' env t))

lookupTy :: (Ord v, MonadTyCheck m) => Env v -> v -> m (TermRef v)
lookupTy env v = case envType env v of
                     Nothing -> throwError (OutOfBounds (envPull env v))
                     Just ty -> return ty


type TyMonad m = WriterT [HoleCtx] m

tyInfer :: (Ord v, Show v, MonadTyCheck m)
        => Env v -> TermRef v -> m (TermRef v, [HoleCtx])
tyInfer env = runWriterT . tyInfer' env

-- TODO this should be never necessary, I should allow holes in data decls
tyInferNH :: (Ord v, Show v, MonadTyCheck m) => Env v -> TermRef v -> m (TermRef v)
tyInferNH env t =
    do (ty, holes) <- tyInfer env t
       case holes of
           [] -> return ty
           (HoleCtx{holeName = hn} : _) -> throwError (UnexpectedHole hn)

tyInfer' :: (Ord v, Show v, MonadTyCheck m)
         => Env v -> TermRef v -> TyMonad m (TermRef v)
tyInfer' _ (Ty r) = return (Ty undefined)
tyInfer' env (V v) = lookupTy env v
tyInfer' env t@(Lam _) = untypedTerm env t
tyInfer' env₁ (Arr ty₁ s) =
    do tyty₁ <- tyInfer' env₁ ty₁
       case whnf env₁ tyty₁ of
           (Ty r₁) -> do let env₂ = nestEnvTy env₁ ty₁; ty₂ = fromScope s
                         tyty₂ <- tyInfer' env₂ ty₂
                         case nf env₂ tyty₂ of
                             (Ty r₂) -> return (Ty undefined)
                             _       -> expectingType env₂ ty₂ tyty₂
           _ -> expectingType env₁ ty₁ tyty₁
tyInfer' env (App t₁ t₂) =
    do tyt₁ <- tyInfer' env t₁
       case whnf env tyt₁ of
           Arr ty₁ s -> do tyCheck env t₂ ty₁; return (instantiate1 t₂ s)
           _         -> expectingFunction env t₁ tyt₁
tyInfer' env (Canon dc ts) = tyInfer' env (app (V (envNest env dc) : ts))
tyInfer' env (Elim en ts) = tyInfer' env (app (V (envNest env en) : ts))
tyInfer' env (Ann ty t) = do tyCheck env ty (Ty undefined); ty <$ tyCheck env t ty
tyInfer' env t@(Hole _ _) = untypedTerm env t

tyCheck :: (Ord v, Show v, MonadTyCheck m)
         => Env v -> TermRef v -> TermRef v -> TyMonad m ()
tyCheck env₀ t₀ ty₀ = go env₀ t₀ (nf env₀ ty₀)
  where
    go :: (Ord v, Show v, MonadTyCheck m)
       => Env v -> TermRef v -> TermRef v -> TyMonad m ()
    go env (Lam s₁) (Arr ty s₂) =
        go (nestEnvTy env ty) (fromScope s₁) (fromScope s₂)
    go env (Hole hn ts) ty =
        do tys <- mapM (tyInfer' env) ts
           tell [runFresh (formHole env hn ty (zip ts tys))]
    go env t ty = do tyt <- nf env <$> tyInfer' env t
                     unless (ty == tyt) (mismatch env ty t tyt)
