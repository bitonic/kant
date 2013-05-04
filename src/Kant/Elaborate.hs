{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
-- | This is largely ripped off fig. 9 of 'The View from the Left'.
module Kant.Elaborate (Elaborate(..)) where

import           Control.Arrow ((***), second)
import           Control.Monad (when, unless)
import           Data.List (elemIndex)
import           Data.Maybe (isJust)

import           Control.Monad.Identity (Identity, runIdentity)

import           Bound
import           Bound.Name
import qualified Data.HashSet as HashSet
import           Data.Proxy

import           Data.Bwd
import           Kant.ADT
import           Kant.Common
import           Kant.Cursor
import           Kant.Decl
import           Kant.Env
import           Kant.Monad
import           Kant.Term
import           Kant.TyCheck
#include "../impossible.h"

class Elaborate a where
    elaborate :: Monad m => a -> KMonadT Id m [HoleCtx]

instance r ~ Ref => Elaborate (Decl r) where
    elaborate (Val n t) =
        do checkDup n
           (ty, holes) <- tyInfer t
           holes <$ addFreeM n ty (Just t)
    elaborate (Postulate n ty) =
        do checkDup n
           (_, holes) <- tyInfer ty
           holes <$ addFreeM n ty Nothing
    -- TODO normalise all types before elaborating
    elaborate (ADTD (tyc, tycty) dcs) =
        do checkDup tyc
           -- Check that the type of the tycon is well typed
           tyInferNH tycty
           -- Check that the type constructor returns a type
           unless (returnsTy tycty) (expectingTypeCon tyc tycty)
           -- Add the type of the tycon to scope
           addFreeM tyc tycty Nothing
           -- Create the functions that will form 'ADTCon's
           mapM (\(dc, dcty) -> elabCon tyc dc dcty) dcs
           eltyR <- freshRef
           let elty  = runElabM (elimTy tyc tycty dcs eltyR) -- D-elim type
               eln   = elimName tyc                          -- D-elim name
               -- Function that will form the 'ADTRewr's
               elfun = typedLam (Data (ADTRewr tyc)) elty
           addFreeM eln elty (Just elfun)
           -- Add the actual ADT
           [] <$ addADTM tyc ADT{ adtName = tyc
                                , adtTy   = tycty
                                , adtRewr = buildRewr (arrLen tycty) tyc dcs
                                , adtCons = dcs }
    elaborate (RecD (tyc, tycty) dc projs) =
        do checkDup tyc
           -- Tycheck type con
           tyInferNH tycty
           -- Returns a type...
           unless (returnsTy tycty) (expectingTypeCon tyc tycty)
           -- Add the tycon
           addFreeM tyc tycty Nothing
           -- Add the projections types
           let projns = map fst projs
           -- Note that it is important to add the projections in this order, so
           -- that we typecheck them with regards to the previous fields only.
           projtys <- mapM (elabRecProj tyc tycty projns) projs
           -- Finally, add the data constructor
           elabRecCon tyc dc tycty projs
           [] <$ addRecM tyc Record{ recName  = tyc
                                   , recTy    = tycty
                                   , recProjs = projtys
                                   , recRewr  = buildRecRewr projns }
returnsTy :: TermRef v -> Bool
returnsTy (Arr  _ s) = returnsTy (fromScope s)
returnsTy (Ty _)     = True
returnsTy _          = False

elabCon :: Monad m
        => ConId           -- ^ Tycon name
        -> ConId           -- ^ Name of the datacon
        -> TermRefId       -- ^ Type of the datacon
        -> KMonadT Id m ()
elabCon tyc dc ty =
    do checkDup dc
       tyInferNH ty -- The type of the datacon is well typed
       fromKMonadP (goodTy B0 ty) -- ...and well formed
       let t = typedLam (Data (ADTCon dc)) ty -- Function that forms the 'ADTCon'
       addFreeM dc ty (Just t)
  where
    goodTy :: (VarC v, Monad m) => Bwd v -> TermRef v -> KMonadP v m ()
    goodTy vs (Arr arg s) =
        do -- If the type constructor appears in the type, then it must be at
           -- the top level.
           env <- getEnv
           let fvs  = freeVs env arg
           unless (not (HashSet.member tyc fvs) || appHead arg == V (nest env tyc))
                  (wrongRecTypePos dc tyc ty)
           nestPM (goodTy (bmap F vs :< B dummyN) (fromScope s))
    goodTy vs (appV -> (arg, pars)) =
        -- The type must return something of the type we are defininng, and the
        -- tycon must be applied to the parameters, in order.
        do env <- getEnv
           unless (arg == V (nest env tyc) &&
                   and (zipWith (==) pars (map V (toList vs))))
                  (expectingTypeData dc tyc ty)

type ElabM v a = KMonad (Cursor Proxy) v Identity a

runElabM :: ElabM Id a -> a
runElabM m = case runIdentity (runKMonad newCurs m) of
                 Left err     -> IMPOSSIBLE("Got error from KMonad:\n" ++ show err)
                 Right (x, _) -> x

-- TODO better argument names.
elimTy :: ConId                 -- ^ Tycon
       -> TermRefId             -- ^ Tycon type
       -> [(ConId, TermRefId)]  -- ^ Constructors
       -> Ref                   -- ^ Reference for the returned Ty
       -> ElabM Id TermRefId
elimTy tyc tycty cons ref = telescope targetsf tycty
  where
    targetsf :: Eq v => [v] -> ElabM v (TermRef v)
    targetsf args =
        -- Then scope a "motive", which is a predicate on D, so we need to scope
        -- again all the parameters plus an instance of D with those parameters.
        do curs <- getEnv
           let targs   = map V args
               motive  = nestt (mkArr (app (V (nest curs tyc) : targs)) (Ty ref))
               -- The variable that will refer to the motive
               motiveV = V (B (Name "P" ()))
               -- The arguments to the result of the functions, which will be `P
               -- args x' where args are the arguments for D and x is the instance
               -- of D. Note that the variable refers to the thing scoped just
               -- before the motive: `x'.
               target  = V (F (B (Name "x" ())))
           mkArr (app (V (nest curs tyc) : targs)) <$>
                 (mkArr motive <$>
                  nestPM (nestPM (methods (map (F . F) args) motiveV target cons)))

    methods :: Eq v
            => [v]                  -- Arguments for the tycon
            -> TermRef v            -- Quantified motive `P'
            -> TermRef v            -- Target
            -> [(ConId, TermRefId)] -- Constructors
            -> ElabM v (TermRef v)
    methods _ motiveV target [] = return (app [motiveV, target])
    methods args motiveV target ((dc, dcty) : dcs) =
        mkArr <$> method args dc dcty motiveV
              <*> nestPM (methods (map F args) (nestt motiveV) (nestt target) dcs)

    -- I can't use `telescope' because I need to bump the motiveV each time
    method :: Eq v
           => [v]               -- Arguments to the tycon
           -> ConId             -- Data con
           -> TermRefId         -- Data con type
           -> TermRef v         -- Quantifiend motive `P'
           -> ElabM v (TermRef v)
    method args₀ dc dcty motiveV₀ =
        let go :: Eq v
               => TermRef v        -- Quantified motive `P'
               -> [v]              -- Args for the tycon
               -> [(v, TermRef v)] -- Args to the datacon, var and type
               -> TermRef v        -- Type of the datacon
               -> ElabM v (TermRef v)
            go motiveV tyargs args (Arr arg s) =
                mkArr arg <$>
                nestPM (go (nestt motiveV) (map F tyargs)
                           (map (F *** nestt) args ++ [(B (bindingN s), nestt arg)])
                           (fromScope s))
            go motiveV tyargs args (appV -> _) =
                do curs <- getEnv
                   hyps dc motiveV
                        (app (V (nest curs dc) : map V tyargs ++ map (V . fst) args))
                        args
        in do curs <- getEnv
              go motiveV₀ args₀ [] (discharge args₀ (nest curs <$> dcty))

    discharge [] dcty = dcty
    discharge (arg : args) (Arr _ s) = discharge args (instantiate1 (V arg) s)
    discharge _ _ = IMPOSSIBLE("collected arguments don't match type")

    hyps :: Eq v
         => ConId
         -> TermRef v            -- Quantified motive `P'
         -> TermRef v            -- Argument for the motive
         -> [(v, TermRef v)]     -- Quantified args of the constructors, with types
         -> ElabM v (TermRef v)
    hyps _ motiveV motiveArg [] = return (app [motiveV, motiveArg])
    hyps dc motiveV motiveArg ((argv, (appV -> (tyh, _))) : args) =
        do curs <- getEnv
           if tyh == V (cursNest curs tyc)
             then mkArr (app [motiveV, V argv]) <$>
                        nestPM (hyps dc (nestt motiveV) (nestt motiveArg)
                                     (map (F *** nestt) args))
             else hyps dc motiveV motiveArg args

buildRewr :: Int -> ConId -> [(ConId, TermRefId)] -> Rewr
-- The `i' is the number of parameters for the tycon, the first 1 for the
-- motive, the second for the target, the third for the number of
-- constructors.
buildRewr i _ dcs ts | length ts /= i + 1 + 1 + length dcs =
    IMPOSSIBLE("got wrong number of arguments in rewrite")
buildRewr i tyc dcs (ts :: [TermRef v]) =
    case t of
        -- TODO should we assert that the arguments are of the right number?
        Data (ADTCon dc) args | Just j <- elemIndex dc (map fst dcs) ->
            let method = methods !! j; dcty = snd (dcs !! j)
            in Just (app (method : drop i args ++ recs 0 args dcty))
        Data (ADTCon dc) _ -> IMPOSSIBLE("constructor not present: " ++ dc)
        _ -> Nothing
  where
    (pars, (t : motive : methods)) = splitAt i ts

    recs :: Int -> [TermRef v] -> TermRefId -> [TermRef v]
    recs n args (Arr (appV -> (tyHead, _)) s) =
        (if tyHead == V tyc then [recuRewr (args !! n)] else []) ++
         -- It doesn't matter what we instantiate here
        recs (n+1) args (instDummy s)
    recs _ _ _ = []

    recuRewr x = Data (ADTRewr tyc) (pars ++ [x, motive] ++ methods)

elimName :: ConId -> Id
elimName tyc = tyc ++ "-Elim"

checkDup :: (VarC v, Monad m) => Id -> KMonadT v m ()
checkDup v =
    do env <- getEnv
       when (isJust (envType env (nest env v))) (duplicateName v)

nestt :: Functor f => f a -> f (Var b a)
nestt = fmap F

mkArr :: TermRef v -> TermRef (Var (NameId ()) v) -> TermRef v
mkArr  t₁ t₂ = Arr t₁ (toScope t₂)

instDummy :: TermScopeRef Id -> TermRefId
instDummy s = instantiate1 (V "dummy") s

-- | Provided with a @(x1 : S1) -> ... -> (xn : Sn) -> T@ returns a
--   @(x1 : S1) -> ... -> (xn : Sn) -> f [x1..xn]@.
telescope :: Eq v
          => (forall a. Eq a => [a] -> ElabM a (TermRef a))
          -> TermRef v -> ElabM v (TermRef v)
telescope f = go B0
  where
    go :: Eq v => Bwd v -> TermRef v -> ElabM v (TermRef v)
    go vs (Arr ty s) =
        Arr ty <$> (toScope <$> nestPM (go (bmap F vs :< B (bindingN s)) (fromScope s)))
    go vs _ = f (toList vs)

-- | Provided with a @A = (x1 : S1) -> ... -> (xn : Sn) -> T@ returns a
--   @(\x1 .. xn  => f [x1..xn]) : A@.
typedLam :: (forall a. [TermRef a] -> TermRef a) -> TermRefId -> TermRefId
typedLam f ty = Ann ty (runElabM (go B0 ty))
  where
    go :: Eq v => Bwd v -> TermRef v -> ElabM v (TermRef v)
    go vs (Arr _ s) =
        Lam <$> (toScope <$> nestPM (go (bmap F vs :< B (bindingN s)) (fromScope s)))
    go vs _ = return (f (map V (toList vs)))

elabRecCon :: Monad m => ConId -> ConId -> TermRefId -> Projs Ref -> KMonadT Id m ()
elabRecCon tyc dc tycty projs =
    do let dcty = runElabM (go₁ B0 tycty)
       -- TODO make sure that I typecheck everywhere like here but assert it,
       -- since if we generate an ill typed type it's an internal error.
       tyInferNH dcty
       addFreeM dc dcty (Just (typedLam (Data (RecCon dc)) dcty))
  where
    go₁ :: VarC v => Bwd v -> TermRef v -> ElabM v (TermRef v)
    go₁ vs (Arr ty s) =
        let par = B (bindingN s)
        in  Arr ty <$>
            (toScope <$> nestPM (go₁ (bmap F vs :< par) (fromScope s)))
    go₁ vs _ =
        do env <- getEnv
           go₂ vs (instProjs (toList vs) (map (second (fmap (nest env))) projs))

    go₂ :: VarC v => Bwd v -> [(Id, TermRef v)] -> ElabM v (TermRef v)
    go₂ vs [] =
        do env <- getEnv
           return (app (V (nest env tyc) : map V (toList vs)))
    go₂ vs ((n, proj) : pjs) =
        do env <- getEnv
           let abproj v = if v == nest env n then Just (Name n ()) else Nothing
               pjs' = map (second (fromScope . abstract abproj)) pjs
           Arr proj <$> (toScope <$> nestPM (go₂ (bmap F vs) pjs'))

elabRecProj :: Monad m
            => ConId                       -- Type con
            -> TermRefId                   -- Type con type
            -> [Id   ]                     -- Projection names
            -> (Id, Scope Int TermRef Id)  -- Current projection
            -> KMonadT Id m (Id, TermRefId)
elabRecProj tyc tycty projns (n, proj) =
    do let projty = runElabM (go B0 tycty)
       tyInferNH projty
       addFreeM n projty Nothing
       return (n, projty)
  where
    go :: VarC v => Bwd v -> TermRef v -> ElabM v (TermRef v)
    go vs (Arr ty s) =
        Arr ty <$> (toScope <$> nestPM (go (bmap F vs :< B (bindingN s)) (fromScope s)))
    go vs _ =
        do env <- getEnv
           let vs' = toList vs
           Arr (app (map V (nest env tyc : vs'))) . toScope <$> nestPM (returnTy vs')

    returnTy :: VarC v => [v] -> ElabM (Var (NameId ()) v) (TermRef (Var (NameId ()) v))
    returnTy (map F -> vs) =
        do env' <- getEnv
           let fixprojs v = if v `elem` map (nest env') projns
                            then app (map V (v : vs ++ [B (Name "x" ())]))
                            else V v
           return (fixprojs =<< (instProj vs (nest env' <$> proj)))

instProj :: [v] -> Scope Int TermRef v  -> TermRef v
instProj vs s = instantiate inst s
  where
    inst i = if i < length vs then V (vs !! i)
             else IMPOSSIBLE("Out of bound index in projection")

instProjs :: [v] -> [(Id, Scope Int TermRef v)] -> [(Id, TermRef v)]
instProjs vs = map (second (instProj vs))

buildRecRewr :: [Id] -> Id -> Rewr
buildRecRewr projs pr [Data (RecCon _) ts]
    | Just ix <- ixm, length projs == length ts = Just (ts !! ix)
    | Nothing <- ixm = IMPOSSIBLE("projection not present: " ++ pr)
    | otherwise = IMPOSSIBLE("wrong number of record arguments")
  where ixm = elemIndex pr projs
buildRecRewr _ _ [_] = Nothing
-- TODO could it be that ill-typed expressions can lead to this?  In which case
-- it might be better not to throw an error.
buildRecRewr _ _ _ = IMPOSSIBLE("got more than one argument")

instance r ~ Ref => Elaborate (Module r) where
    elaborate = go [] . unModule
      where
        go holes []             = return holes
        go holes (decl : decls) = do holes' <- elaborate decl
                                     go (holes ++ holes') decls
