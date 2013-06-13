{-# LANGUAGE ViewPatterns #-}
module Kant.TyCheck (tyInfer, tyInferNH) where

import           Control.Monad (unless, join)

import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Writer (WriterT(..), MonadWriter(..))

import           Bound
import           Data.Proxy

import           Data.Constraint (Constr(..))
import           Kant.Common
import           Kant.Cursor
import           Kant.Monad
import           Kant.Term
#include "../impossible.h"

tyInfer :: (VarC v, Monad m) => TmRef v -> KMonadT v m (TmRef v, [HoleCtx])
tyInfer t =
    do (ty, holes) <- mapKMonad run (tyInfer' t)
       return (ty, reverse holes)
  where
    run m = do (x, hs) <- runWriterT m
               return $ case x of
                            Left err        -> Left err
                            Right (y, env)  -> Right ((y, hs), env)

-- TODO this should be never necessary, I should allow holes in data decls
tyInferNH :: (VarC v, Monad m) => TmRef v -> KMonadT v m (TmRef v)
tyInferNH t =
    do (ty, holes) <- tyInfer t
       case holes of
           []                           -> return ty
           (HoleCtx{holeName = hn} : _) -> unexpectedHole hn

type TyMonad f v m = KMonadE f v (WriterT [HoleCtx] m)
type TyMonadP v m = TyMonad Proxy v m
type TyMonadT v m = TyMonad TmRef v m

addHole :: Monad m => HoleCtx -> TyMonad f v m ()
addHole hole = lift (tell [hole])

tyInfer' :: (VarC v, Monad m) => TmRef v -> TyMonadT v m (TmRef v)
tyInfer' (Ty r) = Ty <$> addConstr' (r :<:)
tyInfer' (V v) = constrIfTy =<< lookupTy v
tyInfer' t@(Lam _) = untypedTm t
tyInfer' (Arr ty₁ s) =
    do tyty₁@(Ty r₁) <- Ty <$> freshRef
       tyCheck ty₁ tyty₁
       nestM ty₁ $ do tyty₂@(Ty r₂) <- Ty <$> freshRef
                      tyCheck (fromScope s) tyty₂
                      Ty <$> addConstrs' (\r -> [r₁ :<=: r, r₂ :<=: r])
tyInfer' (App t₁ t₂) =
    do tyt₁ <- tyInfer' t₁
       tyt₁' <- whnfM tyt₁
       case tyt₁' of
           Arr ty₁ s -> do tyCheck t₂ ty₁
                           constrIfTy (instantiate1 t₂ s)
           _         -> expectingFunction t₁ tyt₁
tyInfer' t@(Con _ tyc _ _) =
    do tyc' <- (`nest` tyc) <$> getEnv
       tycty <- lookupTy tyc'
       if arrLen tycty == 0 then return (V tyc') else untypedTm t
tyInfer' (Destr ar tyc n t) =
    do tyt  <- tyInfer' t
       pars <- checkTyCon tyc tyt
       destrTy <- case ar of
                      ADT_ -> lookupElim tyc
                      Rec_ -> lookupProj tyc n
       return (discharge (pars ++ [t]) destrTy)
tyInfer' (Ann ty t) =
    do tyCheck ty . Ty =<< freshRef
       ty <$ tyCheck t ty
tyInfer' t@(Hole _ _) = untypedTm t
tyInfer' (Prop r) = Prop <$> addConstr' (r :<:)
tyInfer' Top = Prop <$> freshRef
tyInfer' Bot = Prop <$> freshRef
tyInfer' (And pr₁ pr₂) =
    do r₁ <- freshRef
       r₂ <- freshRef
       tyCheck pr₁ (Prop r₁)
       tyCheck pr₂ (Prop r₂)
       Prop <$> addConstrs' (\r -> [r₁ :<=: r, r₂ :<=: r])
tyInfer' (Forall ty s) =
    do tyty@(Ty r₁) <- Ty <$> freshRef
       tyCheck ty tyty
       nestM tyty $ do tys@(Prop r₂) <- Prop <$> freshRef
                       tyCheck (fromScope s) tys
                       Prop <$> addConstrs' (\r -> [r₁ :<=: r, r₂ :<=: r])
tyInfer' (Dec pr) =
    do prty@(Prop r) <- Prop <$> freshRef
       tyCheck pr prty
       return (Ty r)
tyInfer' (Coeh c ty₁ ty₂ q t) =
    do ty₁ty <- Ty <$> freshRef
       tyCheck ty₁ ty₁ty
       ty₂ty <- Ty <$> freshRef
       tyCheck ty₂ ty₂ty
       tyCheck q (Dec (Eq ty₁ ty₁ty ty₂ ty₂ty))
       tyCheck t ty₁
       case c of
           Coe -> return ty₂
           Coh -> return (Dec (Eq t ty₁ (coe ty₁ ty₁ q t) ty₂))
tyInfer' (Eq t₁ ty₁ t₂ ty₂) =
    do tyCheck t₁ ty₁
       ty₁ty@(Ty r₁) <- Ty <$> freshRef
       tyCheck ty₁ ty₁ty
       tyCheck t₂ ty₂
       ty₂ty@(Ty r₂) <- Ty <$> freshRef
       tyCheck ty₂ ty₂ty
       Prop <$> addConstrs' (\r -> [r₁ :<=: r, r₂ :<=: r])

checkTyCon :: (Monad m, VarC v) => ConId -> TmRef v -> TyMonadT v m [TmRef v]
checkTyCon tyc t =
    do t' <- whnfM t
       case appV t' of
           (V v, ts) -> do env <- getEnv
                           if nest env tyc == v
                              then return ts
                              else expectingTypeData tyc t
           _         -> expectingTypeData tyc t

-- We don't bother checking that the parameters are of the right type since we
-- already know that that's the case.
-- TODO maybe assert the assumption above.
discharge :: VarC v => [TmRef v] -> TmRef v -> TmRef v
discharge []       ty        = ty
discharge (t : ts) (Arr _ s) = discharge ts (instantiate1 t s)
discharge _        ty        = IMPOSSIBLE("Expecting arrow instead of " ++ show ty)

constrIfTy :: (VarC v, Monad m) => TmRef v -> KMonadE f v m (Tm Ref v)
constrIfTy ty =
    do ty' <- whnfM ty
       case ty' of
           Ty r -> Ty <$> addConstr' (r :<=:)
           _    -> return ty

tyCheck :: (VarC v, Monad m) => TmRef v -> TmRef v -> TyMonadT v m ()
tyCheck = whnf₂ go
  where
    go :: (VarC v, Monad m) => TmRef v -> TmRef v -> TyMonadT v m ()
    go (Con ar tyc dc ts) ty =
        do pars <- checkTyCon tyc ty
           dcty <- discharge pars <$> lookupDataCon ar tyc dc
           checkDataCon ts dcty
    go (Lam s₁) (Arr ty s₂) = nestM ty (whnf₂ go (fromScope s₁) (fromScope s₂))
    go (Hole hn ts) ty =
        do tys <- mapM tyInfer' ts
           addHole =<< formHoleM hn ty =<< (zip <$> mapM nfM ts <*> mapM nfM tys)
    go (Ty r₁) (Ty r₂) = addConstrs [r₁ :<: r₂]
    go t ty =
        do tyt <- whnfM =<< tyInfer' t
           eq <- fromKMonadP (eqRefs ty tyt)
           unless eq (mismatch ty t tyt)

checkDataCon :: (VarC v, Monad m) => [TmRef v] -> TmRef v -> TyMonadT v m ()
checkDataCon [] _ = return ()
checkDataCon (t : ts) (Arr ty s) =
    do tyCheck t ty
       checkDataCon ts (instantiate1 t s)
checkDataCon _ ty = IMPOSSIBLE("Expecting arrow instead of " ++ show ty)

-- TODO maybe find a way to eliminate the explicit recursion?
eqRefs :: (VarC v, Monad m) => TmRef v -> TmRef v -> TyMonadP v m Bool
eqRefs (V v₁) (V v₂) = return (v₁ == v₂)
eqRefs (Ty r₁) (Ty r₂) = do addConstrs [r₁ :==: r₂]; return True
eqRefs (Lam s₁) (Lam s₂) = nestPM (eqRefs' (fromScope s₁) (fromScope s₂))
eqRefs (Arr ty₁ s₁) (Arr ty₂ s₂) =
    (&&) <$> eqRefs ty₁ ty₂
         <*> nestPM (eqRefs' (fromScope s₁) (fromScope s₂))
eqRefs (App t₁ t'₁) (App t₂ t'₂) = (&&) <$> eqRefs t₁ t₂ <*> eqRefs t'₁ t'₂
eqRefs (Ann ty₁ t₁) (Ann ty₂ t₂) = (&&) <$> eqRefs ty₁ ty₂ <*> eqRefs t₁ t₂
eqRefs (Con ar₁ tyc₁ dc₁ ts₁) (Con ar₂ tyc₂ dc₂ ts₂) =
     (((ar₁, tyc₁, dc₁) == (ar₂, tyc₂, dc₂) &&) . and) <$>
     mapM (uncurry eqRefs) (zip ts₁ ts₂)
eqRefs (Destr ar₁ tyc₁ n₁ t₁) (Destr ar₂ tyc₂ n₂ t₂) =
    ((ar₁, tyc₁, n₁) == (ar₂, tyc₂, n₂) &&) <$> eqRefs t₁ t₂
eqRefs (Hole x _) (Hole y _) = return (x == y)
eqRefs _ _ = return False

eqRefs' :: (VarC v, Monad m) => TmRef v -> TmRef v -> TyMonadP v m Bool
eqRefs' = whnf₂ eqRefs

whnf₂ :: (Monad m, VarC v) => (TmRef v -> TmRef v -> TyMonad f v m a)
      -> TmRef v -> TmRef v -> TyMonad f v m a
whnf₂ m t₁ t₂ = join (m <$> whnfM t₁ <*> whnfM t₂)
