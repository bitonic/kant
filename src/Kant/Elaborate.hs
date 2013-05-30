{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
-- | This is largely ripped off fig. 9 of 'The View from the Left'.
module Kant.Elaborate (Elaborate(..), elimName) where

import           Control.Arrow ((***), second)
import           Control.Monad (when, unless)
import           Data.Foldable (foldlM)
import           Data.List (elemIndex)
import           Data.Maybe (isJust)
import           Data.Foldable (forM_)

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
           holes <$ addFreeM n (Value ty t)
    elaborate (Postulate n ty) =
        do checkDup n
           (_, holes) <- tyInfer ty
           holes <$ addFreeM n (Abstract ty)
    -- TODO normalise all types before elaborating
    elaborate (ADTD (tyc, tycty) dcs) =
        do checkDup tyc
           -- Check that the type of the tycon is well typed
           tyInferNH tycty
           -- Check that the type constructor returns a type
           unless (returnsTy tycty) (expectingTypeCon tyc tycty)
           -- Add the type of the tycon to scope
           addFreeM tyc (Abstract tycty)
           -- Create the functions that will form 'ADTCon's
           mapM (\(dc, dcty) -> elabCon tyc dc dcty) dcs
           eltyR <- freshRef
           let elty = runElabM (elimTy tyc tycty dcs eltyR) -- D-elim type
           -- Add the elim to the env
           addFreeM (elimName tyc) (DataElim tyc)
           -- Add the actual ADT
           [] <$ addADTM tyc ADT{ adtName = tyc
                                , adtTy   = tycty
                                , adtElim = elty
                                , adtRewr = buildRewr (arrLen tycty) tyc dcs
                                , adtCons = dcs }
    elaborate (RecD (tyc, tycty) dc projs) =
        -- This is a bit tricky, since we need the 'RecCon's in the env to
        -- typecheck the projections, if we add the bodies of the tycon and the
        -- projs themselves.  Thus, we gradually replace the 'Rec' with a more
        -- complete version.
        do checkDup tyc
           -- Tycheck type con
           tyInferNH tycty
           -- Returns a type...
           unless (returnsTy tycty) (expectingTypeCon tyc tycty)
           -- Add the tycon
           addFreeM tyc (Abstract tycty)
           -- Add the record
           let projns = map fst projs
               rec = Rec{ recName  = tyc
                        , recTy    = tycty
                        , recCon   = IMPOSSIBLE("we haven't added the dc yet")
                        , recProjs = []
                        , recRewr  = buildRecRewr projns }
               addProj (elprojs, rec₁) proj@(projn, _) =
                   do projty <- elabRecRewr tyc dc tycty projns proj
                      let elproj = (projn, projty)
                          rec₂ = rec₁{recProjs = recProjs rec₁ ++ [(projn, projty)]}
                      addRecM tyc rec₂
                      return (elprojs ++ [elproj], rec₂)
           addRecM tyc rec
           -- We add the projection one by one, gradually upgrading the rec.
           (_, rec') <- foldlM addProj ([], rec) projs
           -- Finally, add the data constructor
           dcty <- elabRecCon tyc dc tycty projs
           [] <$ addRecM tyc rec'{recCon   = (dc, dcty)}

returnsTy :: TmRef v -> Bool
returnsTy (Arr  _ s) = returnsTy (fromScope s)
returnsTy (Ty _)     = True
returnsTy _          = False

elabCon :: Monad m
        => ConId         -- ^ Tycon name
        -> ConId         -- ^ Name of the datacon
        -> TmRefId       -- ^ Type of the datacon
        -> KMonadT Id m ()
elabCon tyc dc ty =
    do checkDup dc
       tyInferNH ty -- The type of the datacon is well typed
       fromKMonadP (goodTy B0 ty) -- ...and well formed
       -- Add it to the env
       addFreeM dc (DataCon tyc)
  where
    goodTy :: (VarC v, Monad m) => Bwd v -> TmRef v -> KMonadP v m ()
    goodTy vs (Arr arg s) =
        do -- If the type constructor appears in the type, then it must be at
           -- the top level.
           env <- getEnv
           let fvs  = freeVs env arg
           unless (not (HashSet.member tyc fvs) || appHead arg == V (nest env tyc))
                  (wrongRecTypePos tyc dc)
           nestPM (goodTy (fmap F vs :< B dummyN) (fromScope s))
    goodTy vs (appV -> (arg, pars)) =
        -- The type must return something of the type we are defininng, and the
        -- tycon must be applied to the parameters, in order.
        do env <- getEnv
           unless (arg == V (nest env tyc) &&
                   and (zipWith (==) pars (map V (toList vs))))
                  (expectingTypeData' dc tyc ty)

type ElabM v a = KMonad (Cursor Proxy) v Identity a

runElabM :: ElabM Id a -> a
runElabM m = case runIdentity (runKMonad newCurs m) of
                 Left err     -> IMPOSSIBLE("Got error from KMonad:\n" ++ show err)
                 Right (x, _) -> x

elimTy :: ConId               -- ^ Tycon
       -> TmRefId             -- ^ Tycon type
       -> [(ConId, TmRefId)]  -- ^ Constructors
       -> Ref                 -- ^ Reference for the returned Ty
       -> ElabM Id TmRefId
elimTy tyc tycty cons ref = telescope targetsf tycty
  where
    targetsf :: Eq v => [v] -> ElabM v (TmRef v)
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
            => [v]                -- Arguments for the tycon
            -> TmRef v            -- Quantified motive `P'
            -> TmRef v            -- Target
            -> [(ConId, TmRefId)] -- Constructors
            -> ElabM v (TmRef v)
    methods _ motiveV target [] = return (app [motiveV, target])
    methods args motiveV target ((dc, dcty) : dcs) =
        mkArr <$> method args dc dcty motiveV
              <*> nestPM (methods (map F args) (nestt motiveV) (nestt target) dcs)

    -- I can't use `telescope' because I need to bump the motiveV each time
    method :: Eq v
           => [v]             -- Arguments to the tycon
           -> ConId           -- Data con
           -> TmRefId         -- Data con type
           -> TmRef v         -- Quantifiend motive `P'
           -> ElabM v (TmRef v)
    method args₀ dc dcty motiveV₀ =
        let go :: Eq v
               => TmRef v        -- Quantified motive `P'
               -> [(v, TmRef v)] -- Args to the datacon, var and type
               -> TmRef v        -- Type of the datacon
               -> ElabM v (TmRef v)
            go motiveV args (Arr arg s) =
                mkArr arg <$>
                nestPM (go (nestt motiveV)
                           (map (F *** nestt) args ++ [(B (bindingN s), nestt arg)])
                           (fromScope s))
            go motiveV args (appV -> _) =
                hyps dc motiveV (Con ADT_ tyc dc (map (V . fst) args)) args
        in do curs <- getEnv
              go motiveV₀ [] (discharge args₀ (nest curs <$> dcty))

    discharge [] dcty = dcty
    discharge (arg : args) (Arr _ s) = discharge args (instantiate1 (V arg) s)
    discharge _ _ = IMPOSSIBLE("collected arguments don't match type")

    hyps :: Eq v
         => ConId
         -> TmRef v            -- Quantified motive `P'
         -> TmRef v            -- Argument for the motive
         -> [(v, TmRef v)]     -- Quantified args of the constructors, with types
         -> ElabM v (TmRef v)
    hyps _ motiveV motiveArg [] = return (app [motiveV, motiveArg])
    hyps dc motiveV motiveArg ((argv, (appV -> (tyh, _))) : args) =
        do curs <- getEnv
           if tyh == V (cursNest curs tyc)
             then mkArr (app [motiveV, V argv]) <$>
                        nestPM (hyps dc (nestt motiveV) (nestt motiveArg)
                                     (map (F *** nestt) args))
             else hyps dc motiveV motiveArg args

buildRewr :: Int -> ConId -> [(ConId, TmRefId)] -> Rewr_
-- The 1 is for the target, then the number of methods
buildRewr _ _ dcs _ ts | length ts < 1 + length dcs = Nothing
buildRewr pars tyc dcs (t :: TmRef v) ts =
    case t of
        Con ADT_ _ dc args | Just j <-  elemIndex dc (map fst dcs) ->
            let method = methods !! j
                dcty   = snd (dcs !! j)
            in Just (app (method : args ++ recs pars args dcty) : rest)
        Con ADT_ _ dc _ -> IMPOSSIBLE("constructor not present: " ++ dc)
        _ -> Nothing
  where
    (motive : methods, rest) = splitAt (1 + length dcs) ts

    -- Here we are using the datacon type to find out about recursive
    -- occurences, so for example it doesn't really matter what we instantiate
    recs 0 (arg : args) (Arr (appV -> (tyHead, _)) s) =
        (if tyHead == V tyc then [recuRewr arg] else []) ++
        recs 0 args (instDummy s)
    recs 0 [] _ = []
    recs n args (Arr _ s) = recs (n - 1) args (instDummy s)
    recs _ _ _ = IMPOSSIBLE("malformed data type")

    recuRewr x = app (Destr ADT_ tyc (elimName tyc) x : motive : methods)

elimName :: ConId -> Id
elimName tyc = tyc ++ "-Elim"

checkDup :: (VarC v, Monad m) => Id -> KMonadT v m ()
checkDup v =
    do env <- getEnv
       when (isJust (envType env (nest env v))) (duplicateName v)

nestt :: Functor f => f a -> f (Var b a)
nestt = fmap F

mkArr :: TmRef v -> TmRef (Var NameId v) -> TmRef v
mkArr  t₁ t₂ = Arr t₁ (toScope t₂)

instDummy :: TmScopeRef Id -> TmRefId
instDummy s = instantiate1 (V "dummy") s

-- | Provided with a @(x1 : S1) -> ... -> (xn : Sn) -> T@ returns a
--   @(x1 : S1) -> ... -> (xn : Sn) -> f [x1..xn]@.
telescope :: Eq v
          => (forall a. Eq a => [a] -> ElabM a (TmRef a))
          -> TmRef v -> ElabM v (TmRef v)
telescope f = go B0
  where
    go :: Eq v => Bwd v -> TmRef v -> ElabM v (TmRef v)
    go vs (Arr ty s) =
        Arr ty <$> (toScope <$> nestPM (go (fmap F vs :< B (bindingN s)) (fromScope s)))
    go vs _ = f (toList vs)

elabRecCon :: Monad m => ConId -> ConId -> TmRefId -> Projs Ref -> KMonadT Id m TmRefId
elabRecCon tyc dc tycty projs =
    do let dcty = runElabM (go₁ B0 tycty)
       -- TODO make sure that I typecheck everywhere like here but assert it,
       -- since if we generate an ill typed type it's an internal error.
       tyInferNH dcty
       -- Add it to the env
       addFreeM dc (RecCon tyc)
       return dcty
  where
    go₁ :: VarC v => Bwd v -> TmRef v -> ElabM v (TmRef v)
    go₁ vs (Arr ty s) =
        let par = B (bindingN s)
        in  Arr ty <$>
            (toScope <$> nestPM (go₁ (fmap F vs :< par) (fromScope s)))
    go₁ vs _ =
        do env <- getEnv
           go₂ vs (instProjs (toList vs) (map (second (fmap (nest env))) projs))

    go₂ :: VarC v => Bwd v -> [(Id, TmRef v)] -> ElabM v (TmRef v)
    go₂ vs [] =
        do env <- getEnv
           return (app (V (nest env tyc) : map V (toList vs)))
    go₂ vs ((n, proj) : pjs) =
        do env <- getEnv
           let abproj v = if v == nest env n then Just (Name n ()) else Nothing
               pjs' = map (second (fromScope . abstract abproj)) pjs
           Arr proj <$> (toScope <$> nestPM (go₂ (fmap F vs) pjs'))

elabRecRewr :: (Monad m)
            => ConId                     -- Type con
               -> ConId                  -- Data con
            -> TmRefId                   -- Type con type
            -> [Id]                      -- Projection names
            -> Proj Ref                  -- Current projection
            -> KMonadT Id m TmRefId
elabRecRewr tyc dc tycty projns (n, proj) =
    do -- we need to check recursive occurrences here, it's very annoying
       -- because ideally we'd just avoid adding the record in the first place.
       forM_ proj $
           \v -> do env <- getEnv
                    when (v == nest env tyc) (wrongRecTypePos tyc dc)
       let projty = runElabM (go B0 tycty)
       tyInferNH projty
       addFreeM n (RecProj tyc)
       return projty
  where
    go :: VarC v => Bwd v -> TmRef v -> ElabM v (TmRef v)
    go vs (Arr ty s) =
        Arr ty <$>
        (toScope <$> nestPM (go (fmap F vs :< B (bindingN s)) (fromScope s)))
    go vs _ =
        do env <- getEnv
           let vs' = toList vs
           Arr (app (map V (nest env tyc : vs'))) . toScope <$> nestPM (returnTy vs')

    returnTy :: VarC v => [v] -> ElabM (Var NameId v) (TmRef (Var NameId v))
    returnTy (map F -> vs) =
        do env' <- getEnv
           let fixprojs v = case free' env' v of
                                Just pn | pn `elem` projns ->
                                    Destr Rec_ tyc pn (V (B (Name "x" ())))
                                _ -> V v
           return (fixprojs =<< instProj vs (nest env' <$> proj))

instProj :: [v] -> Scope (Name Id Int) TmRef v -> TmRef v
instProj vs s = instantiate inst s
  where
    inst (Name _ i) = if i < length vs then V (vs !! i)
                      else IMPOSSIBLE("Out of bound index in projection")

instProjs :: [v] -> [(Id, Scope (Name Id Int) TmRef v)] -> [(Id, TmRef v)]
instProjs vs = map (second (instProj vs))

buildRecRewr :: [Id] -> Id -> Rewr_
buildRecRewr projs pr (Con Rec_ _ _ ts) rest
    | Just ix <- ixm, length projs == length ts = Just (ts !! ix : rest)
    | Nothing <- ixm = IMPOSSIBLE("projection not present: " ++ pr)
    | otherwise = IMPOSSIBLE("wrong number of record arguments")
  where ixm = elemIndex pr projs
buildRecRewr _ _ _ _ = Nothing

instance r ~ Ref => Elaborate (Module r) where
    elaborate = go [] . unModule
      where
        go holes []             = return holes
        go holes (decl : decls) = do holes' <- elaborate decl
                                     go (holes ++ holes') decls
