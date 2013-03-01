{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.Elaborate (elaborate) where

import           Control.Monad (when, unless)
import           Data.Foldable (foldrM)
import           Data.List (elemIndex)
import           Data.Maybe (isJust)

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
                  env₃ <- foldrM (\(dc, dty) env₃ -> elaborateCon env₃ tyc dc dty)
                                 env₂ cons
                  ety <- elimTy env₃ tyc cty cons
                  let en = elimName tyc
                      env₄ = addFree env₃ en Nothing (Just ety)
                  return (addElim env₄ en (buildElim (arrLen cty) tyc cons))
          else throwError (ExpectingTypeCon tyc cty)
  where
    returnsTy :: Term v -> Bool
    returnsTy (Arr (Abs _ s)) = returnsTy (fromScope s)
    returnsTy Ty              = True
    returnsTy _               = False

elaborateCon :: MonadTyCheck m
             => EnvId
             -> ConId           -- ^ Type constructor name
             -> ConId           -- ^ Name of the datacon
             -> TermId          -- ^ Type of the datacon
             -> m EnvId
elaborateCon env tyc dc ty =
    do checkDup env dc
       tyCheck env ty
       goodTy env ty
       return (addFree env dc (Just (buildCanon [] ty)) (Just ty))
  where
    goodTy :: (Ord v, Show v, MonadTyCheck m) => Env v -> Term v -> m ()
    goodTy env' (Arr (Abs ty' s)) =
        do let fvs  = envFreeVs env' ty'
           unless (not (Set.member tyc fvs) || appHead ty' == V (envNest env' tyc))
                  (wrongRecTypePos env dc tyc ty)
           goodTy (nestEnv env' Nothing Nothing) (fromScope s)
    goodTy env' (appV -> AppV t _) =
        unless (t == V (envNest env' tyc)) (expectingTypeData env dc tyc ty)

    buildCanon :: [v] -> Term v -> Term v
    buildCanon vs (Arr (Abs ty' s)) =
        Lam (Abs ty' (toScope (buildCanon (B (bindingN s) : map F vs) (fromScope s))))
    buildCanon vs _ = Canon dc (reverse (map V vs))

elimTy :: MonadTyCheck m
       => EnvId
       -> ConId                 -- ^ Tycon
       -> TermId                -- ^ Tycon type
       -> [(ConId, TermId)]     -- ^ Constructors
       -> m TermId
elimTy _ _ _ _ = return Ty

buildElim :: Int -> ConId -> [(ConId, TermId)] -> Elim
-- The `i' is the number of parameters for the tycon, the first 1 for the
-- motive, the second for the destructured, the third for the number of
-- constructors.
buildElim i _ dcs ts | length ts /= i + 1 + 1 + length dcs =
    error "buildElim: got wrong number of arguments in eliminator"
buildElim i tyc cons (ts :: [Term v]) =
    case des of
        Canon dc ts' | Just j <- elemIndex dc (map fst cons) ->
            let method = methods !! j; dcty = snd (cons !! j)
            -- newEnv, since we only need to pull out the type constructor
            in Just (app (method : ts' ++ recs 0 newEnv dcty))
        Canon _ _ -> error "buildElim: constructor not present"
        _ -> Nothing
  where
    (pars, (des : motive : methods)) = splitAt i ts

    recs :: Eq a => Int -> Env a -> Term a -> [Term v]
    recs n env' (Arr (Abs (appV -> AppV ty' _) s)) =
        (if ty' == V (envNest env' tyc) then [recElim (methods !! n)] else []) ++
        recs (n+1) (nestEnv env' Nothing Nothing) (fromScope s)
    recs _ _ _ = []

    recElim x = Elim (elimName tyc) (pars ++ [x, motive] ++ methods)

elimName :: ConId -> Id
elimName tyc = tyc ++ "-Elim"

checkDup :: (Eq v, MonadTyCheck m) => Env v -> v -> m ()
checkDup env v = when (isJust (envType env v) || isJust (envValue env v))
                      (throwError (DuplicateName (envPull env v)))
