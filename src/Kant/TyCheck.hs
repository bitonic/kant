{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
module Kant.TyCheck
    ( TyCheckError(..)
    , expectingTypeData
    , wrongRecTypePos
    , MonadTyCheck
    , tyCheck
    ) where

import           Control.Applicative (Applicative, (<$>))
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
    deriving (Eq, Show)

instance Error TyCheckError

class (Functor m, Applicative m, MonadError TyCheckError m) => MonadTyCheck m
instance MonadTyCheck (ErrorT TyCheckError IO)

mismatch :: (Ord v, MonadTyCheck m) => Env v -> Term v -> Term v -> Term v -> m a
mismatch env t₁ t₂ t₃ =
    let [t₁', t₂', t₃'] = slam env [t₁, t₂, t₃] in throwError (Mismatch t₁' t₂' t₃')

expectingType :: (Ord v, MonadTyCheck m) => Env v -> Term v -> Term v -> m a
expectingType env t ty =
    let [t', ty'] = slam env [t, ty] in throwError (ExpectingType t' ty')

expectingFunction :: (Ord v, MonadTyCheck m) => Env v -> Term v -> Term v -> m a
expectingFunction env t ty =
    let [t', ty'] = slam env [t, ty] in throwError (ExpectingFunction t' ty')

expectingTypeData :: (Ord v, MonadTyCheck m, Show v)
                  => Env v -> ConId -> ConId -> Term v -> m a
expectingTypeData env dc tyc ty  =
    throwError (ExpectingTypeData dc tyc (slam' env ty))

wrongRecTypePos :: (Ord v, MonadTyCheck m) => Env v -> ConId -> ConId -> Term v -> m a
wrongRecTypePos env dc tyc ty = throwError (WrongRecTypePos dc tyc (slam' env ty))

lookupTy :: (Ord v, MonadTyCheck m) => Env v -> v -> m (Term v)
lookupTy env v = case envType env v of
                     Nothing -> throwError (OutOfBounds (envPull env v))
                     Just ty -> return ty

tyCheck :: (Ord v, Show v, MonadTyCheck m) => Env v -> Term v -> m (Term v)
tyCheck _ Ty = return Ty
tyCheck env (V v) = lookupTy env v
tyCheck env (Lam (Abs ty s)) =
    do tyty <- tyCheck env ty
       case nf env tyty of
           Ty -> Arr . Abs ty . toScope <$>
                 tyCheck (nestEnvTy env ty) (fromScope s)
           _ -> expectingType env ty tyty
tyCheck env₁ (Arr (Abs ty₁ s)) =
    do tyty₁ <- tyCheck env₁ ty₁
       case whnf env₁ tyty₁ of
           Ty -> do let env₂ = nestEnvTy env₁ ty₁; ty₂ = fromScope s
                    tyty₂ <- tyCheck env₂ ty₂
                    case nf env₂ tyty₂ of
                        Ty -> return Ty
                        _ -> expectingType env₂ ty₂ tyty₂
           _ -> expectingType env₁ ty₁ tyty₁
tyCheck env (App t₁ t₂) =
    do tyt₁ <- tyCheck env t₁
       case whnf env tyt₁ of
           Arr (Abs ty₁ s) ->
               do tyCheckEq env ty₁ t₂
                  return (instantiate1 t₂ s)
           _ -> expectingFunction env t₁ tyt₁

-- | @tyCheckEq ty t@ thecks that the term @t@ has type @ty@.
tyCheckEq :: (Ord v, Show v, MonadTyCheck m) => Env v -> Term v -> Term v -> m ()
tyCheckEq env ty t =
    do ty' <- tyCheck env t
       unless (ty' == ty) (mismatch env ty t ty')
