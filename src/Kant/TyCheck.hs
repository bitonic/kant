module Kant.TyCheck
    ( tyInfer
    , tyInferNH
    ) where

import           Control.Monad (unless)

import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Writer (WriterT(..), MonadWriter(..))

import           Bound

import           Kant.Common
import           Kant.Env
import           Kant.Term
import           Kant.Monad
import           Kant.Constraint (Constr(..))

type TyMonad v m = KMonad v (WriterT [HoleCtx] m)

addHole :: Monad m => HoleCtx -> TyMonad v m ()
addHole hole = lift (tell [hole])

tyInfer :: (VarC v, Monad m) => TermRef v -> KMonad v m (TermRef v, [HoleCtx])
tyInfer t =
    do (ty, holes) <- mapKMonad run (tyInfer' t)
       return (ty, reverse holes)
  where
    run m = do (x, hs) <- runWriterT m
               return $ case x of
                            Left err        -> Left err
                            Right (y, env)  -> Right ((y, hs), env)

-- TODO this should be never necessary, I should allow holes in data decls
tyInferNH :: (VarC v, Monad m) => TermRef v -> KMonad v m (TermRef v)
tyInferNH t =
    do (ty, holes) <- tyInfer t
       case holes of
           []                           -> return ty
           (HoleCtx{holeName = hn} : _) -> unexpectedHole hn

tyInfer' :: (VarC v, Monad m) => TermRef v -> TyMonad v m (TermRef v)
tyInfer' (Ty r) = Ty <$> addConstr' (r :<:)
tyInfer' (V v) = lookupTy v
tyInfer' t@(Lam _) = untypedTerm t
tyInfer' (Arr ty₁ s) =
    do tyty₁ <- tyInfer' ty₁
       tyty₁' <- whnfM tyty₁
       case tyty₁' of
           Ty r₁ -> nestEnvTyM ty₁ $
                    do let ty₂ = fromScope s
                       tyty₂ <- tyInfer' ty₂
                       tyty₂' <- nfM tyty₂
                       case tyty₂' of
                           (Ty r₂) -> Ty <$>
                                      addConstrs' (\r -> [r₁ :<=: r, r₂ :<=: r])
                           _       -> expectingType ty₂ tyty₂
           _ -> expectingType ty₁ tyty₁
tyInfer' (App t₁ t₂) =
    do tyt₁ <- tyInfer' t₁
       tyt₁' <- whnfM tyt₁
       case tyt₁' of
           Arr ty₁ s -> do tyCheck t₂ ty₁; return (instantiate1 t₂ s)
           _         -> expectingFunction t₁ tyt₁
tyInfer' (Canon dc ts) = do env <- getEnv; tyInfer' (app (V (envNest env dc) : ts))
tyInfer' (Elim en ts) = do env <- getEnv; tyInfer' (app (V (envNest env en) : ts))
tyInfer' (Ann ty t) = do tyCheck ty . Ty =<< freshRef; ty <$ tyCheck t ty
tyInfer' t@(Hole _ _) = untypedTerm t

tyCheck :: (VarC v, Monad m) => TermRef v -> TermRef v -> TyMonad v m ()
tyCheck t₀ ty₀ = go t₀ =<< nfM ty₀
  where
    go :: (VarC v, Monad m) => TermRef v -> TermRef v -> TyMonad v m ()
    go (Lam s₁) (Arr ty s₂) =
        nestEnvTyM ty (go (fromScope s₁) (fromScope s₂))
    go (Hole hn ts) ty =
        do tys <- mapM tyInfer' ts
           addHole =<< formHoleM hn ty (zip ts tys)
    go t ty =
        do tyt <- nfM =<< tyInfer' t
           eq <- eqRefs ty tyt
           unless eq (mismatch ty t tyt)

-- TODO maybe find a way to eliminate the explicit recursion?
eqRefs :: (VarC v, Monad m) => TermRef v -> TermRef v -> TyMonad v m Bool
eqRefs (V v₁) (V v₂) = return (v₁ == v₂)
eqRefs (Ty r₁) (Ty r₂) = do addConstrs [r₁ :==: r₂]; return True
eqRefs (Lam s₁) (Lam s₂) =
    nestEnvM Nothing Nothing $ eqRefs (fromScope s₁) (fromScope s₂)
eqRefs (Arr ty₁ s₁) (Arr ty₂ s₂) =
    (&&) <$> eqRefs ty₁ ty₂
         <*> nestEnvM Nothing Nothing (eqRefs (fromScope s₁) (fromScope s₂))
eqRefs (App t₁ t'₁) (App t₂ t'₂) = (&&) <$> eqRefs t₁ t₂ <*> eqRefs t'₁ t'₂
eqRefs (Ann ty₁ t₁) (Ann ty₂ t₂) = (&&) <$> eqRefs ty₁ ty₂ <*> eqRefs t₁ t₂
eqRefs (Canon c₁ ts₁) (Canon c₂ ts₂) =
    ((c₁ == c₂ &&) . and) <$> mapM (uncurry eqRefs) (zip ts₁ ts₂)
eqRefs (Elim c₁ ts₁) (Elim c₂ ts₂) =
    ((c₁ == c₂ &&) . and) <$> mapM (uncurry eqRefs) (zip ts₁ ts₂)
eqRefs (Hole x _) (Hole y _) = return (x == y)
eqRefs _ _ = return False
