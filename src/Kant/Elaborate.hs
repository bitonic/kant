{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.Elaborate (Elaborate(..)) where

import           Control.Applicative ((<$>))
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

class Elaborate a where
    elaborate :: MonadTyCheck m => EnvId -> a -> m EnvId

instance Elaborate Decl where
    elaborate env (Val n t) =
        do checkDup env n; ty <- tyCheck env t;
           return (addFree env n (Just t) (Just ty))
    elaborate env (Postulate n ty) =
        do checkDup env n; tyCheck env ty; return (addFree env n Nothing (Just ty))
    elaborate env₁ (Data tyc cty cons) =
        do tyCheck env₁ cty
           if returnsTy cty
              then do let env₂ = addFree env₁ tyc Nothing (Just cty)
                      env₃ <- foldrM (\(dc, dty) env₃ -> elaborateCon env₃ tyc dc dty)
                                     env₂ cons
                      let ety  = elimTy tyc cty cons
                          en   = elimName tyc
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
       return (addFree env dc (Just (buildCanon ty)) (Just ty))
  where
    goodTy :: (Ord v, Show v, MonadTyCheck m) => Env v -> Term v -> m ()
    goodTy env' (Arr (Abs ty' s)) =
        do let fvs  = envFreeVs env' ty'
           unless (not (Set.member tyc fvs) || appHead ty' == V (envNest env' tyc))
                  (wrongRecTypePos env dc tyc ty)
           goodTy (neste₁ env') (fromScope s)
    goodTy env' (appV -> AppV t _) =
        unless (t == V (envNest env' tyc)) (expectingTypeData env dc tyc ty)

    buildCanon = telescope (\_ -> Canon dc) Lam newEnv

elimTy :: ConId                 -- ^ Tycon
       -> TermId                -- ^ Tycon type
       -> [(ConId, TermId)]     -- ^ Constructors
       -> TermId
elimTy tyc tycty cons = targets tycty
  where
    targets = telescope targetsf Arr newEnv
    targetsf env₁ ts =
        let motive     = nestt₁ (telescope motivef Arr env₁ (envNest env₁ <$> tycty))
            motiveV    = V (B dummyN)
            env₂       = neste₂ env₁
            motiveArgs = map nestt₂ ts ++ [V (F (B dummyN))]
        in mkArr (app (V (envNest env₁ tyc) : ts))
                 (mkArr motive (methods env₂ motiveV motiveArgs cons))
    motivef env ts = mkArr (app (V (envNest env tyc) : ts)) Ty

    methods :: Env v -> Term v -> [Term v] -> [(ConId, TermId)] -> Term v
    methods _ motiveV ts [] = app (motiveV : ts)
    methods env motiveV ts ((dc, ty) : cons') =
        mkArr (method env dc motiveV [] (envNest env <$> ty))
              (methods (neste₁ env) (nestt₁ motiveV) (map nestt₁ ts) cons')

    -- I can't use `telescope' because I need to bump the motiveV each time
    method :: Env v -> ConId -> Term v -> [v] -> Term v -> Term v
    method env dc motiveV vs (Arr (Abs ty s)) =
        mkArr ty (method (neste₁ env) dc (nestt₁ motiveV)
                         (map F vs ++ [B (bindingN s)]) (fromScope s))
    method env dc motiveV vs (appV -> AppV _ pars) =
        app [app (motiveV : pars), app (V (envNest env dc) : map V vs)]

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

neste₁ :: Env v -> Env (Var (NameId ()) v)
neste₁ env = nestEnv env Nothing Nothing

neste₂ :: Env v -> Env (Var (NameId ()) (Var (NameId ()) v))
neste₂ = neste₁ . neste₁

nestt₁ :: Functor f => f a -> f (Var b a)
nestt₁ = fmap F

nestt₂ :: Functor f => f a -> f (Var b (Var b a))
nestt₂ = fmap (F . F)

mkArr :: Term v -> Term (Var (NameId ()) v) -> Term v
mkArr  t₁ t₂ = Arr (Abs t₁ (toScope t₂))

telescope :: (forall a. Env a -> [Term a] -> Term a)
          -> (forall a. Abs a -> Term a)
          -> Env v -> Term v -> Term v
telescope f g env' = go env' []
  where
    go :: Env v -> [v] -> Term v -> Term v
    go env vs (Arr (Abs ty s)) =
        g (Abs ty (toScope (go (neste₁ env) (B (bindingN s) : map F vs)
                               (fromScope s))))
    go env vs _ = f env (map V (reverse vs))

instance Elaborate Module where
    elaborate e = go e . unModule
      where go env []             = return env
            go env (decl : decls) = (`go` decls) =<< elaborate env decl
