-- TODO I seem to override global names, check.
-- | Module with various function to convert a term nested in scopes to a
--   top-level thing, taking care of avoiding name-clashes.
--
--   It basically takes the names provided by the user originally, and changes
--   them if there are duplicates.
module Kant.Uniquify (slam, formHole) where

import           Control.Monad (when, void)
import           Data.Maybe (fromMaybe)
import           Data.Traversable (mapM)
import           Prelude hiding (mapM)

import           Control.Monad.State (MonadState(..), evalState, State)

import           Bound
import           Bound.Name
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap

import           Kant.Common
import           Kant.Cursor
import           Kant.Term
#include "../containers.h"

type FreshMonad v = State (HashMap v Id, HashMap Id Integer)

collectFree :: VarC v => CursorP v -> Tm r v -> FreshMonad v ()
collectFree env t = void (mapM go t)
  where go v = when (free env v) (addVar env v)

addVar :: VarC v => CursorP v -> v -> FreshMonad v ()
addVar env v =
    do (names, ixs) <- get
       case HashMap.lookup v names of
           Nothing -> let (n', ixs') = addVar' (cursPull env v) ixs
                      in  put (HashMap.insert v n' names, ixs')
           Just _  -> return ()

addVar' :: Id -> HashMap Id Integer -> (Id, HashMap Id Integer)
addVar' n ixs = (n', HashMap.insert n (ix+1) ixs)
  where
    ix = fromMaybe 0 (HashMap.lookup n ixs)
    n' = n ++ if ix /= 0 then show ix else ""

freshVar :: VarC v => CursorP v -> v -> HashMap v Id -> v
freshVar env v names = cursRename env v (const HMBANG(v, names))

uniquify :: VarC v => CursorP v -> Tm r v -> FreshMonad v (Tm r v)
uniquify env t =
    do collectFree env t
       mapM (addVar env) t
       (names, ixs) <- get
       let t' = t >>= \v -> V (freshVar env v names)
       return (evalState (go t') ixs)
  where
    go t'@(V _) = return t'
    go t'@(Ty _) = return t'
    go (Arr ty s) = Arr <$> go ty <*> goScope s
    go (Lam s) = Lam <$> goScope s
    go (App t₁ t₂) = App <$> go t₁ <*> go t₂
    go (Con ar tyc dc ts') = Con ar tyc dc <$> mapM go ts'
    go (Destr ar tyc n t') = Destr ar tyc n <$> go t'
    go (Ann ty t') = Ann <$> go ty <*> go t'
    go (Hole hn ts) = Hole hn <$> mapM go ts
    go (Eq t₁ ty₁ t₂ ty₂)  = Eq <$> go t₁ <*> go ty₁ <*> go t₂ <*> go ty₂
    go (Coeh c ty₁ ty₂ q t') = Coeh c <$> go ty₁ <*> go ty₂ <*> go q <*> go t'
    go (Prop r) =  return (Prop r)
    go Top = return Top
    go Bot = return Bot
    go (And pr₁ pr₂) = And <$> go pr₁ <*> go pr₂
    go (Forall ty' s) = Forall <$> go ty' <*> goScope s
    go (Dec pr) = Dec <$> go pr

    goScope :: VarC v => TmScope r v -> State (HashMap Id Integer) (TmScope r v)
    goScope s =
        case binding s of
            Nothing -> toScope <$> go (fromScope s)
            Just (Name n ()) ->
                do ixs <- get
                   let (n', ixs') = addVar' n ixs
                       v' = B (Name n' ())
                   put ixs' *> (toScope <$> go (substitute v' (V v') (fromScope s)))
                            <* put ixs

slam' :: VarC v => CursorP v -> Tm r v -> FreshMonad v (TmId r)
slam' env t = (cursPull env <$>) <$> uniquify env t

formHole' :: VarC v
          => CursorP v -> Ref -> HoleId -> TmRef v -> [(TmRef v, TmRef v)]
          -> FreshMonad v (HoleCtx)
formHole' env ref hn goal ts =
    do hctx <- sequence [(,) <$> slam' env t <*> slam' env ty | (t, ty) <- ts]
       goal' <- slam' env goal
       return HoleCtx{holeRef = ref, holeName = hn, holeGoal = goal', holeCtx = hctx}

runFresh :: FreshMonad v a -> a
runFresh s = evalState s (HashMap.empty, HashMap.empty)

slam :: (VarC v, IsCursor c) => c f v -> Tm r v -> TmId r
slam env t = runFresh (slam' (toP (getCurs env)) t)

formHole :: (VarC v, IsCursor c)
         => c f v -> Ref -> HoleId -> TmRef v -> [(TmRef v, TmRef v)]
         -> HoleCtx
formHole env ref hn goal ts = runFresh (formHole' (toP (getCurs env)) ref hn goal ts)
