{-# LANGUAGE FlexibleContexts #-}
module Kant.TyCheck
    ( TyCheckError(..)
    , MonadTyCheck
    , tyCheck
    ) where

import           Control.Applicative (Applicative, (<$>))
import           Control.Monad (unless)

import           Control.Monad.Error (MonadError(..), Error)

import           Bound

import           Kant.Environment
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
    deriving (Eq, Show)

instance Error TyCheckError

class (Functor m, Applicative m, MonadError TyCheckError m) => MonadTyCheck m

mismatch :: (Ord v, MonadTyCheck m) => Env v -> Term v -> Term v -> Term v -> m a
mismatch env t₁ t₂ t₃ =
    let [t₁', t₂', t₃'] = slam env [t₁, t₂, t₃] in throwError (Mismatch t₁' t₂' t₃')

expectingType :: (Ord v, MonadTyCheck m) => Env v -> Term v -> Term v -> m a
expectingType env t ty =
    let [t', ty'] = slam env [t, ty] in throwError (ExpectingType t' ty')

expectingFunction :: (Ord v, MonadTyCheck m) => Env v -> Term v -> Term v -> m a
expectingFunction env t ty =
    let [t', ty'] = slam env [t, ty] in throwError (ExpectingFunction t' ty')

lookupTy :: (Ord v, MonadTyCheck m) => Env v -> v -> m (Term v)
lookupTy env v = case envType env v of
                     Nothing -> throwError (OutOfBounds (envPull env v))
                     Just ty -> return ty

tyCheck :: (Ord v, Show v, MonadTyCheck m) => Env v -> Term v -> m (Term v)
tyCheck _ (Ty l) = return (Ty (l+1))
tyCheck env (V v) = lookupTy env v
tyCheck env (Lam (Abs ty s)) =
    do tyty <- tyCheck env ty
       case nf env tyty of
           Ty _ -> Arr . Abs ty . toScope <$>
                   tyCheck (nestEnvTy env ty) (fromScope s)
           _ -> expectingType env ty tyty
tyCheck env₁ (Arr (Abs ty₁ s)) =
    do tyty₁ <- tyCheck env₁ ty₁
       case whnf env₁ tyty₁ of
           Ty l₁ -> do let env₂ = nestEnvTy env₁ ty₁; ty₂ = fromScope s
                       tyty₂ <- tyCheck env₂ ty₂
                       case nf env₂ tyty₂ of
                           Ty l₂ -> return (Ty (max l₁ l₂))
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
       eqb <- eqCum env ty' ty
       unless eqb (mismatch env ty t ty')

-- | @'eqCum' ty₁ ty₂@ checks if ty₁ is equal to ty₂, including cumulativity.
--   For example @'eqCum' ('Type' 1) ('Type' 4)@ will succeed, but @'eqCum'
--   ('Type' 4) ('Type' 1)@ will fail.
eqCum :: (Ord v, MonadTyCheck m) => Env v -> Term v -> Term v -> m Bool
eqCum env t₁ t₂ = return $ case (t₁', t₂') of
                               (Ty l₁, Ty l₂) -> l₁ <= l₂
                               _              -> t₁' == t₂'
  where t₁' = nf env t₁; t₂' = nf env t₂
