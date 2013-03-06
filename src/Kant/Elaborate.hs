{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
-- | This is largely ripped off fig. 9 of 'The View from the Left'.
module Kant.Elaborate (Elaborate(..)) where

import           Control.Applicative ((<$>))
import           Control.Monad (when, unless)
import           Data.Foldable (foldrM)
import           Data.List (elemIndex)
import           Data.Maybe (isJust)

import           Control.Monad.Error (MonadError(..))
import qualified Data.Set as Set

import           Bound
import           Bound.Name

import           Kant.Term
import           Kant.Decl
import           Kant.Env
import           Kant.TyCheck

class Elaborate a where
    elaborate :: MonadTyCheck m => EnvId -> a -> m EnvId

instance Elaborate Decl where
    elaborate env (Val n t) =
        do checkDup env n; ty <- tyInfer env t;
           return (addFree env n (Just t) (Just ty))
    elaborate env (Postulate n ty) =
        do checkDup env n; tyInfer env ty; return (addFree env n Nothing (Just ty))
    elaborate env₁ (Data tyc tycty dcs) =
        do tyInfer env₁ tycty
           if returnsTy tycty
              then do let env₂ = addFree env₁ tyc Nothing (Just tycty)
                      -- Create the functions that will form 'Canon's
                      env₃ <- foldrM (\(dc, dcty) env₃ ->
                                       elaborateCon env₃ tyc dc dcty)
                                     env₂ dcs
                      let elty = elimTy tyc tycty dcs -- D-elim type
                          eln  = elimName tyc         -- D-elim name
                          -- Function that will form the 'Elim's
                          elt  = typedLam (Elim eln) elty
                          env₄ = addFree env₃ eln (Just elt)  (Just elty)
                      return (addElim env₄ eln (buildElim (arrLen tycty) tyc dcs))
              else throwError (ExpectingTypeCon tyc tycty)
      where
        -- Check that the type constructor returns a type
        returnsTy :: Term v -> Bool
        returnsTy (Arr  _ s) = returnsTy (fromScope s)
        returnsTy Ty         = True
        returnsTy _          = False

elaborateCon :: MonadTyCheck m
             => EnvId
             -> ConId           -- ^ Type constructor name
             -> ConId           -- ^ Name of the datacon
             -> TermId          -- ^ Type of the datacon
             -> m EnvId
elaborateCon env tyc dc ty =
    do checkDup env dc
       tyInfer env ty
       goodTy env ty
       let t = typedLam (Canon dc) ty
       return (addFree env dc (Just t) (Just ty))
  where
    goodTy :: (Ord v, Show v, MonadTyCheck m) => Env v -> Term v -> m ()
    goodTy env' (Arr arg s) =
        do -- If the type constructor appears in the type, then it must be at
           -- the top level.
           let fvs  = envFreeVs env' arg
           unless (not (Set.member tyc fvs) || appHead arg == V (envNest env' tyc))
                  (wrongRecTypePos env dc tyc ty)
           goodTy (neste₁ env') (fromScope s)
    goodTy env' (appV -> (arg, _)) =
        unless (arg == V (envNest env' tyc)) (expectingTypeData env dc tyc ty)

elimTy :: ConId                 -- ^ Tycon
       -> TermId                -- ^ Tycon type
       -> [(ConId, TermId)]     -- ^ Constructors
       -> TermId
elimTy tyc tycty cons = targets tycty
  where
    -- First scope the arguments of the type constructor
    targets = telescope targetsf newEnv
    targetsf env₁ args =
        -- Then scope a "motive", which is a predicate on D, so we need to scope
        -- again all the parameters plus an instance of D with those parameters.
        let motive     = nestt₁ (telescope motivef env₁ (envNest env₁ <$> tycty))
            -- The variable that will refer to the motive
            motiveV    = V (B (Name "P" ()))
            env₂       = neste₂ env₁
            -- The arguments to the result of the functions, which will be `P
            -- args x' where args are the arguments for D and x is the instance
            -- of D. Note that the variable refers to the thing scoped just
            -- before the motive: `x'.
            motiveArgs = map nestt₂ args ++ [V (F (B dummyN))]
        in mkArr (app (V (envNest env₁ tyc) : args))
                 (mkArr motive (methods env₂ motiveV motiveArgs cons))
    motivef env args = mkArr (app (V (envNest env tyc) : args)) Ty

    methods :: Eq v => Env v -> Term v -> [Term v] -> [(ConId, TermId)] -> Term v
    methods _ motiveV args [] = app (motiveV : args)
    methods env motiveV args ((dc, dcty) : dcs) =
        mkArr (method env dc motiveV [] dcty)
              (methods (neste₁ env) (nestt₁ motiveV) (map nestt₁ args) dcs)

    -- I can't use `telescope' because I need to bump the motiveV each time
    method :: Eq v => Env v -> ConId -> Term v -> [v] -> TermId -> Term v
    method env₀ dc motiveV₀ vs₀ dcty =
        let go :: Eq v => Env v -> Term v -> [v] -> Term v -> Term v
            go env motiveV vs (Arr arg s) =
                mkArr arg (go (neste₁ env) (nestt₁ motiveV)
                              (map F vs ++ [B (bindingN s)]) (fromScope s))
            go env motiveV vs (appV -> (_, args)) =
                hyps 0 env (app (motiveV : args)) dc (map V vs) dcty
        in go env₀ motiveV₀ vs₀ (envNest env₀ <$> dcty)

    hyps :: Eq v => Int -> Env v -> Term v -> ConId -> [Term v] -> TermId -> Term v
    hyps i env motive dcty args (Arr (appV -> (ty, _)) s) =
        let rest = instDummy s
        in if ty == V tyc
           then mkArr (app [motive, args !! i])
                      (hyps (i+1) (neste₁ env) (nestt₁ motive) dcty (map nestt₁ args)
                            rest)
           else hyps (i+1) env motive dcty args rest
    hyps _ env motive dcty args _ = app [motive, app (V (envNest env dcty) : args)]

buildElim :: Int -> ConId -> [(ConId, TermId)] -> Elim
-- The `i' is the number of parameters for the tycon, the first 1 for the
-- motive, the second for the destructured, the third for the number of
-- constructors.
buildElim i _ dcs ts | length ts /= i + 1 + 1 + length dcs =
    error "buildElim: got wrong number of arguments in eliminator"
buildElim i tyc dcs (ts :: [Term v]) =
    case t of
        Canon dc args | Just j <- elemIndex dc (map fst dcs) ->
            let method = methods !! j; dcty = snd (dcs !! j)
            -- newEnv, since we only need to pull out the type constructor
            in Just (app (method : args ++ recs 0 args dcty))
        Canon _ _ -> error "buildElim: constructor not present"
        _ -> Nothing
  where
    (pars, (t : motive : methods)) = splitAt i ts

    recs :: Int -> [Term v] -> TermId -> [Term v]
    recs n args (Arr (appV -> (tyHead, _)) s) =
        (if tyHead == V tyc then [recElim (args !! n)] else []) ++
         -- It doesn't matter what we instantiate here
        recs (n+1) args (instDummy s)
    recs _ _ _ = []

    recElim x = Elim (elimName tyc) (pars ++ [x, motive] ++ methods)

elimName :: ConId -> Id
elimName tyc = tyc ++ "-Elim"

checkDup :: (Eq v, MonadTyCheck m) => Env v -> v -> m ()
checkDup env v = when (isJust (envType env v) || isJust (envValue env v))
                      (throwError (DuplicateName (envPull env v)))

neste₁ :: Env v -> Env (Var (NameId ()) v)
neste₁ env = nestEnv' env Nothing Nothing Nothing

neste₂ :: Env v -> Env (Var (NameId ()) (Var (NameId ()) v))
neste₂ = neste₁ . neste₁

nestt₁ :: Functor f => f a -> f (Var b a)
nestt₁ = fmap F

nestt₂ :: Functor f => f a -> f (Var b (Var b a))
nestt₂ = fmap (F . F)

mkArr :: Term v -> Term (Var (NameId ()) v) -> Term v
mkArr  t₁ t₂ = Arr t₁ (toScope t₂)

instDummy :: Scope n Term String -> TermId
instDummy s = instantiate1 (V "dummy") s

telescope :: Eq v
          => (forall a. Eq a => Env a -> [Term a] -> Term a)
          -> Env v -> Term v -> Term v
telescope f env' = go env' []
  where
    go :: Eq v => Env v -> [v] -> Term v -> Term v
    go env vs (Arr ty s) =
        Arr ty (toScope (go (neste₁ env) (B (bindingN s) : map F vs) (fromScope s)))
    go env vs _ = f env (map V (reverse vs))

typedLam :: (forall a. [Term a] -> Term a) -> TermId -> TermId
typedLam f ty = Ann ty (go newEnv [] ty)
  where
    go :: Eq v => Env v -> [v] -> Term v -> Term v
    go env vs (Arr _ s) =
        Lam (toScope (go (neste₁ env) (B (bindingN s) : map F vs) (fromScope s)))
    go _ vs _ = f (map V (reverse vs))

instance Elaborate Module where
    elaborate e = go e . unModule
      where go env []             = return env
            go env (decl : decls) = (`go` decls) =<< elaborate env decl
