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
                  foldrM (\(dc, dty) env₃ -> elaborateCon env₃ tyc cty dc dty)
                         env₂ cons
          else throwError (ExpectingTypeCon tyc cty)
  where
    returnsTy :: Term v -> Bool
    returnsTy (Arr (Abs _ s)) = returnsTy (fromScope s)
    returnsTy Ty              = True
    returnsTy _               = False

elaborateCon :: MonadTyCheck m
             => EnvId
             -> ConId           -- ^ Type constructor name
             -> TermId          -- ^ Type of the tycon
             -> ConId           -- ^ Name of the datacon
             -> TermId          -- ^ Type of the datacon
             -> m EnvId
elaborateCon env₁ tyc tycty dc ty =
    do checkDup env₁ dc
       tyCheck env₁ ty
       goodTy env₁ ty
       let env₂ = addFree env₁ dc (Just (buildCanon 0 ty)) (Just ty)
           ety  = elimTy tycty ty
           et   = buildElim ty
           env₃ = addFree env₂ elimName (Just et) (Just ety)
       return (addElim env₃ elimName elimElim)
  where
    goodTy :: (Ord v, Show v, MonadTyCheck m) => Env v -> Term v -> m TermId
    goodTy env (Arr (Abs ty' s)) =
        do let fvs  = envFreeVs env ty'
           unless (not (Set.member tyc fvs) || appHead ty' == V (envNest env tyc))
                  (wrongRecTypePos env₁ dc tyc ty)
           goodTy (nestEnv env Nothing Nothing) (fromScope s)
    goodTy env (appV -> AppV t _) =
        if t == V (envNest env tyc)
        then undefined
        else expectingTypeData env₁ dc tyc ty

    buildCanon :: Integer -> Term v -> Term v
    buildCanon = undefined

    buildElim :: Term v -> Term v
    buildElim = undefined

    elimElim :: Elim
    elimElim = undefined

    elimTy :: Term v -> Term v -> Term v
    elimTy = undefined

    elimName = tyc ++ "-Elim"

checkDup :: (Eq v, MonadTyCheck m) => Env v -> v -> m ()
checkDup env v =
    when (isJust (envType env v) || isJust (envValue env v))
         (throwError (DuplicateName (envPull env v)))
