{-# LANGUAGE ViewPatterns #-}
module Kant.Elaborate (elaborate) where

import           Control.Monad (when, unless)
import           Data.Maybe (isJust)
import           Data.Foldable (foldrM)

import           Control.Monad.Error (MonadError(..))
import qualified Data.Set as Set

import           Bound

import           Kant.Term
import           Kant.Decl
import           Kant.Env
import           Kant.TyCheck

elaborate :: MonadTyCheck m => EnvId -> Decl -> m EnvId
elaborate env (Val n t) =
    do checkDup env n; ty <- tyCheck env t; return (addFree env n (Just t) (Just ty))
elaborate env (Postulate n ty) =
    do checkDup env n; tyCheck env ty; return (addFree env n Nothing (Just ty))
elaborate env₁ (Data tyc cty cons) =
    do tyCheck env₁ cty
       if returnsTy cty
          then do let env₂ = addFree env₁ tyc Nothing (Just cty)
                  foldrM (\(dc, dty) env₃ -> elaborateCon env₃ tyc dc dty)
                         env₂ cons
          else throwError (ExpectingTypeCon tyc cty)
  where
    returnsTy :: Term v -> Bool
    returnsTy (Arr (Abs _ s)) = returnsTy (fromScope s)
    returnsTy Ty              = True
    returnsTy _               = False

elaborateCon :: MonadTyCheck m
             => EnvId
             -> ConId           -- ^ Return type expected
             -> ConId           -- ^ Name of the datacon
             -> TermId          -- ^ Type of the datacon
             -> m EnvId
elaborateCon env tyc dc ty =
    do checkDup env dc
       tyCheck env ty
       goodTy env ty
       return (addFree env dc Nothing (Just ty))
  where
    goodTy :: (Ord v, Show v, MonadTyCheck m) => Env v -> Term v -> m ()
    goodTy env' (Arr (Abs ty' s)) =
        do let fvs  = envFreeVs env' ty'
           unless (not (Set.member tyc fvs) || appHead ty' == V (envNest env' tyc))
                  (wrongRecTypePos env dc tyc ty)
           goodTy (nestEnv env' Nothing Nothing) (fromScope s)
    goodTy env' (appV -> AppV t _) =
        unless (t == V (envNest env' tyc)) (expectingTypeData env dc tyc ty)

checkDup :: (Eq v, MonadTyCheck m) => Env v -> v -> m ()
checkDup env v =
    when (isJust (envType env v) || isJust (envValue env v))
         (throwError (DuplicateName (envPull env v)))
