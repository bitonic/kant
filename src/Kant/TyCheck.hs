{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.TyCheck
    ( TyCheckError(..)
    , expectingTypeData
    , wrongRecTypePos
    , MonadTyCheck
    , tyInfer
    ) where

import           Control.Applicative (Applicative, (<$>), (<$))
import           Control.Monad (unless)

import           Control.Monad.Error (MonadError(..), Error, ErrorT)

import           Bound

import           Kant.Env
import           Kant.Reduce
import           Kant.Term
import           Kant.Uniquify

data TyCheckError
    = TyCheckError
    | OutOfBounds Id
    | DuplicateName Id
    | Mismatch TermId TermId TermId
    | ExpectingFunction TermId TermId
    | ExpectingType TermId TermId
    | ExpectingTypeCon ConId TermId
    | ExpectingTypeData ConId ConId TermId
    | WrongRecTypePos ConId ConId TermId
    | UntypedTerm TermId
    | DuplicateHole HoleId
    deriving (Eq, Show)

instance Error TyCheckError

class (Functor m, Applicative m, MonadError TyCheckError m) => MonadTyCheck m
instance MonadTyCheck (ErrorT TyCheckError IO)

mismatch :: (Ord v, Show v, MonadTyCheck m)
         => Env v -> Term v -> Term v -> Term v -> m a
mismatch env t₁ t₂ t₃ =
    runFresh $ do [t₁', t₂', t₃'] <- mapM (slam env) [t₁, t₂, t₃]
                  return (throwError (Mismatch t₁' t₂' t₃'))

expectingType :: (Ord v, Show v, MonadTyCheck m) => Env v -> Term v -> Term v -> m a
expectingType env t ty =
    runFresh $ do [t', ty'] <- mapM (slam env) [t, ty]
                  return (throwError (ExpectingType t' ty'))

expectingFunction :: (Ord v, Show v, MonadTyCheck m)
                  => Env v -> Term v -> Term v -> m a
expectingFunction env t ty =
    runFresh $ do [t', ty'] <- mapM (slam env) [t, ty]
                  return (throwError (ExpectingFunction t' ty'))

expectingTypeData :: (Ord v, MonadTyCheck m, Show v)
                  => Env v -> ConId -> ConId -> Term v -> m a
expectingTypeData env dc tyc ty  =
    throwError (ExpectingTypeData dc tyc (slam' env ty))

wrongRecTypePos :: (Ord v, Show v, MonadTyCheck m)
                => Env v -> ConId -> ConId -> Term v -> m a
wrongRecTypePos env dc tyc ty = throwError (WrongRecTypePos dc tyc (slam' env ty))

untypedTerm :: (Ord v, Show v, MonadError TyCheckError m) => Env v -> Term v -> m a
untypedTerm env t = throwError (UntypedTerm (slam' env t))

lookupTy :: (Ord v, MonadTyCheck m) => Env v -> v -> m (Term v)
lookupTy env v = case envType env v of
                     Nothing -> throwError (OutOfBounds (envPull env v))
                     Just ty -> return ty

tyInfer :: (Ord v, Show v, MonadTyCheck m) => Env v -> Term v -> m (Term v)
tyInfer _ Ty = return Ty
tyInfer env (V v) = lookupTy env v
tyInfer env t@(Lam _) = untypedTerm env t
tyInfer env₁ (Arr ty₁ s) =
    do tyty₁ <- tyInfer env₁ ty₁
       case whnf env₁ tyty₁ of
           Ty -> do let env₂ = nestEnvTy env₁ s ty₁; ty₂ = fromScope s
                    tyty₂ <- tyInfer env₂ ty₂
                    case nf env₂ tyty₂ of
                        Ty -> return Ty
                        _  -> expectingType env₂ ty₂ tyty₂
           _ -> expectingType env₁ ty₁ tyty₁
tyInfer env (App t₁ t₂) =
    do tyt₁ <- tyInfer env t₁
       case whnf env tyt₁ of
           Arr ty₁ s -> do tyCheck env t₂ ty₁; return (instantiate1 t₂ s)
           _         -> expectingFunction env t₁ tyt₁
tyInfer env (Canon dc ts) = tyInfer env (app (V (envNest env dc) : ts))
tyInfer env (Elim en ts) = tyInfer env (app (V (envNest env en) : ts))
tyInfer env (Ann ty t) = do tyCheck env ty Ty; ty <$ tyCheck env t ty
tyInfer env t@(Hole _) = untypedTerm env t

tyCheck :: (Ord v, Show v, MonadTyCheck m) => Env v -> Term v -> Term v -> m ()
tyCheck env t ty = tyCheck' env t (nf env ty)

tyCheck' :: (Ord v, Show v, MonadTyCheck m) => Env v -> Term v -> Term v -> m ()
tyCheck' env (Lam s₁) (Arr ty s₂) =
    tyCheck' (nestEnvTy env s₂ ty) (fromScope s₁) (fromScope s₂)
tyCheck' env (Hole hn) ty = undefined
tyCheck' env t ty = do tyt <- nf env <$> tyInfer env t
                       unless (ty == tyt) (mismatch env ty t tyt)
