{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
-- | This is largely ripped off fig. 9 of 'The View from the Left'.
module Kant.Elaborate (Elaborate(..)) where

import           Control.Applicative ((<$>))
import           Control.Arrow ((***))
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
    elaborate :: MonadTyCheck m => EnvId -> a -> m (EnvId, [HoleCtx])

instance r ~ FRef => Elaborate (Decl r) where
    elaborate env (Val n t) =
        do checkDup env n
           (ty, holes) <- tyInfer env t;
           return (addFree env n (Just t) (Just ty), holes)
    elaborate env (Postulate n ty) =
        do checkDup env n
           (tyty, holes) <- tyInfer env ty
           return (addFree env n Nothing (Just tyty), holes)
    -- TODO normalise all types before elaborating
    elaborate env₁ (Data tyc tycty dcs) =
        do checkDup env₁ tyc
           tyInferNH env₁ tycty -- Check that the type of the tycon is well typed
           -- Check that the type constructor returns a type
           unless (returnsTy tycty) (throwError (ExpectingTypeCon tyc (unRef tycty)))
           let -- Add the type of the tycon to scope
               env₂ = addFree env₁ tyc Nothing (Just tycty)
               -- Create the functions that will form 'Canon's
           env₃ <- foldrM (\(dc, dcty) env₃ -> elaborateCon env₃ tyc dc dcty) env₂ dcs
           let elty  = elimTy tyc tycty dcs undefined -- D-elim type
               eln   = elimName tyc                   -- D-elim name
               -- Function that will form the 'Elim's
               elfun = typedLam (Elim eln) elty
               env₄  = addFree env₃ eln (Just elfun)  (Just elty)
               -- Add the actual eliminator
           return (addElim env₄ eln (buildElim (arrLen tycty) tyc dcs), [])
      where
        returnsTy :: TermRef v -> Bool
        returnsTy (Arr  _ s) = returnsTy (fromScope s)
        returnsTy (Ty _)     = True
        returnsTy _          = False

elaborateCon :: MonadTyCheck m
             => EnvId
             -> ConId           -- ^ Tycon name
             -> ConId           -- ^ Name of the datacon
             -> TermRefId       -- ^ Type of the datacon
             -> m EnvId
elaborateCon env tyc dc ty =
    do checkDup env dc
       tyInferNH env ty         -- The type of the datacon is well typed
       goodTy env [] ty         -- ...and well formed
       let t = typedLam (Canon dc) ty -- Function that forms the 'Canon'
       return (addFree env dc (Just t) (Just ty))
  where
    -- TODO Check that we return the D with the right arguments.
    goodTy :: (Ord v, Show v, MonadTyCheck m) => Env v -> [v] -> TermRef v -> m ()
    goodTy env' vs (Arr arg s) =
        do -- If the type constructor appears in the type, then it must be at
           -- the top level.
           let fvs  = envFreeVs env' arg
           unless (not (Set.member tyc fvs) || appHead arg == V (envNest env' tyc))
                  (wrongRecTypePos env dc tyc ty)
           goodTy (neste₁ env') (B dummyN : map F vs) (fromScope s)
    goodTy env' vs (appV -> (arg, pars)) =
        -- The type must return something of the type we are defininng, and the
        -- tycon must be applied to the parameters, in order.
        unless (arg == V (envNest env' tyc) &&
                and (zipWith (==) pars (map V (reverse vs))))
               (expectingTypeData env dc tyc ty)

elimTy :: ConId                 -- ^ Tycon
       -> TermRefId             -- ^ Tycon type
       -> [(ConId, TermRefId)]  -- ^ Constructors
       -> Ref                   -- ^ Reference for the returned Ty
       -> TermRefId
elimTy tyc tycty cons ref = targets tycty
  where
    -- First scope the arguments of the type constructor
    targets = telescope targetsf newEnv

    targetsf :: Eq v => Env v -> [v] -> TermRef v
    targetsf env₁ args =
        -- Then scope a "motive", which is a predicate on D, so we need to scope
        -- again all the parameters plus an instance of D with those parameters.
        let targs      = map V args
            motive     = nestt₁ (mkArr (app (V (envNest env₁ tyc) : targs))
                                       (Ty (Forget ref)))
            -- The variable that will refer to the motive
            motiveV    = V (B (Name "P" ()))
            env₂       = neste₂ env₁
            -- The arguments to the result of the functions, which will be `P
            -- args x' where args are the arguments for D and x is the instance
            -- of D. Note that the variable refers to the thing scoped just
            -- before the motive: `x'.
            target     = V (F (B (Name "x" ())))
        in mkArr (app (V (envNest env₁ tyc) : targs))
                 (mkArr motive (methods env₂ (map (F . F) args) motiveV target cons))

    methods :: Eq v
            => Env v
            -> [v]                  -- Arguments for the tycon
            -> TermRef v            -- Quantified motive `P'
            -> TermRef v            -- Target
            -> [(ConId, TermRefId)] -- Constructors
            -> TermRef v
    methods _ _ motiveV target [] = app [motiveV, target]
    methods env args motiveV target ((dc, dcty) : dcs) =
        mkArr (method env args dc dcty motiveV)
              (methods (neste₁ env) (map F args) (nestt₁ motiveV) (nestt₁ target) dcs)

    -- I can't use `telescope' because I need to bump the motiveV each time
    method :: Eq v
           => Env v
           -> [v]               -- Arguments to the tycon
           -> ConId             -- Data con
           -> TermRefId         -- Data con type
           -> TermRef v         -- Quantifiend motive `P'
           -> TermRef v
    method env₀ args₀ dc dcty motiveV₀ =
        let go :: Eq v => Env v
               -> TermRef v        -- Quantified motive `P'
               -> [v]              -- Args for the tycon
               -> [(v, TermRef v)] -- Args to the datacon, var and type
               -> TermRef v        -- Type of the datacon
               -> TermRef v
            go env motiveV tyargs args (Arr arg s) =
                mkArr arg
                      (go (neste₁ env) (nestt₁ motiveV) (map F tyargs)
                          (map (F *** nestt₁) args ++ [(B (bindingN s), nestt₁ arg)])
                          (fromScope s))
            go env motiveV tyargs args (appV -> _) =
                hyps env dc motiveV
                     (app (V (envNest env dc) : map V tyargs ++ map (V . fst) args))
                     args
        in go env₀ motiveV₀ args₀ [] (discharge args₀ (envNest env₀ <$> dcty))

    discharge [] dcty      = dcty
    discharge (arg : args) (Arr _ s) = discharge args (instantiate1 (V arg) s)
    discharge _ _ = error "Elaborate.discharge: the impossible happened"

    hyps :: Eq v => Env v
         -> ConId
         -> TermRef v            -- Quantified motive `P'
         -> TermRef v            -- Argument for the motive
         -> [(v, TermRef v)]     -- Quantified args of the constructors, with types
         -> TermRef v
    hyps _ _ motiveV motiveArg [] = app [motiveV, motiveArg]
    hyps env dc motiveV motiveArg ((argv, (appV -> (tyh, _))) : args) =
        if tyh == V (envNest env tyc)
        then mkArr (app [motiveV, V argv])
                   (hyps (neste₁ env) dc (nestt₁ motiveV) (nestt₁ motiveArg)
                         (map (F *** nestt₁) args))
        else hyps env dc motiveV motiveArg args

buildElim :: Int -> ConId -> [(ConId, TermRefId)] -> Elim
-- The `i' is the number of parameters for the tycon, the first 1 for the
-- motive, the second for the target, the third for the number of
-- constructors.
buildElim i _ dcs ts | length ts /= i + 1 + 1 + length dcs =
    error "buildElim: got wrong number of arguments in eliminator"
buildElim i tyc dcs (ts :: [TermRef v]) =
    case t of
        -- TODO should we assert that the arguments are of the right number?
        Canon dc (drop i -> args) | Just j <- elemIndex dc (map fst dcs) ->
            let method = methods !! j; dcty = snd (dcs !! j)
            -- newEnv, since we only need to pull out the type constructor
            in Just (app (method : args ++ recs 0 args dcty))
        Canon _ _ -> error "buildElim: constructor not present"
        _ -> Nothing
  where
    (pars, (t : motive : methods)) = splitAt i ts

    recs :: Int -> [TermRef v] -> TermRefId -> [TermRef v]
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
neste₁ env = nestEnv env Nothing Nothing

neste₂ :: Env v -> Env (Var (NameId ()) (Var (NameId ()) v))
neste₂ = neste₁ . neste₁

nestt₁ :: Functor f => f a -> f (Var b a)
nestt₁ = fmap F

mkArr :: TermRef v -> TermRef (Var (NameId ()) v) -> TermRef v
mkArr  t₁ t₂ = Arr t₁ (toScope t₂)

instDummy :: TermScopeRef Id -> TermRefId
instDummy s = instantiate1 (V "dummy") s

-- | Provided with a @(x1 : S1) -> ... -> (xn : Sn) -> T@ returns a
--   @(x1 : S1) -> ... -> (xn : Sn) -> f [x1..xn]@.
telescope :: Eq v
          => (forall a. Eq a => Env a -> [a] -> TermRef a)
          -> Env v -> TermRef v -> TermRef v
telescope f env' = go env' []
  where
    go :: Eq v => Env v -> [v] -> TermRef v -> TermRef v
    go env vs (Arr ty s) =
        Arr ty (toScope (go (neste₁ env) (B (bindingN s) : map F vs) (fromScope s)))
    go env vs _ = f env (reverse vs)

-- | Provided with a @A = (x1 : S1) -> ... -> (xn : Sn) -> T@ returns a
--   @(\x1 .. xn  => f [x1..xn]) : A@.
typedLam :: (forall a. [TermRef a] -> TermRef a) -> TermRefId -> TermRefId
typedLam f ty = Ann ty (go newEnv [] ty)
  where
    go :: Eq v => Env v -> [v] -> TermRef v -> TermRef v
    go env vs (Arr _ s) =
        Lam (toScope (go (neste₁ env) (B (bindingN s) : map F vs) (fromScope s)))
    go _ vs _ = f (map V (reverse vs))

instance r ~ FRef => Elaborate (Module r) where
    elaborate e = go e [] . unModule
      where
        go env holes []             = return (env, holes)
        go env holes (decl : decls) = do (ty, holes') <- elaborate env decl
                                         go ty (holes ++ holes') decls
