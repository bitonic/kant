{-# LANGUAGE ViewPatterns #-}
module Kant.TyCheck
    ( tyInfer
    , tyInferNH
    ) where

import           Control.Monad (unless, join)

import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Writer (WriterT(..), MonadWriter(..))

import           Bound
import           Data.Proxy

import           Data.Constraint (Constr(..))
import           Kant.Common
import           Kant.Monad
import           Kant.Term

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
type TyMonadT v m = TyMonad Param v m

addHole :: Monad m => HoleCtx -> TyMonad f v m ()
addHole hole = lift (tell [hole])

tyInfer' :: (VarC v, Monad m) => TmRef v -> TyMonadT v m (TmRef v)
tyInfer' (Ty r) = Ty <$> addConstr' (r :<:)
tyInfer' (V (Twin v w)) = constrIfTy =<< lookupVar v w
tyInfer' t@(Lam _) = untypedTm t
tyInfer' (Arr ty₁ s) =
    do tyty₁ <- tyInfer' ty₁
       tyty₁' <- whnfM tyty₁
       case tyty₁' of
           Ty r₁ -> nestM (P ty₁) $
                    do let ty₂ = fromScope s
                       tyty₂ <- tyInfer' ty₂
                       tyty₂' <- whnfM tyty₂
                       case tyty₂' of
                           (Ty r₂) -> Ty <$>
                                      addConstrs' (\r -> [r₁ :<=: r, r₂ :<=: r])
                           _       -> expectingType ty₂ tyty₂
           _ -> expectingType ty₁ tyty₁
tyInfer' (App t₁ t₂) = do tyt₁ <- tyInfer' t₁; checkApp (Just t₁) tyt₁ [t₂]
tyInfer' (Data (tyc, TyCon dt) ts)      = dataInfer ts =<< lookupDataTy dt tyc
tyInfer' (Data (tyc, DataCon dt dc) ts) = dataInfer ts =<< lookupDataCon dt tyc dc
tyInfer' (Data (tyc, ADTRewr) ts)       = dataInfer ts =<< lookupElim tyc
tyInfer' (Data (tyc, RecRewr n) ts)     = dataInfer ts =<< lookupProj tyc n
tyInfer' (Ann ty t) = do tyCheck ty . Ty =<< freshRef; ty <$ tyCheck t ty
tyInfer' t@(Hole _ _) = untypedTm t

dataInfer :: (Monad m, VarC v) => [TmRef v] -> TmRef v -> TyMonadT v m (TmRef v)
dataInfer = flip (checkApp Nothing)

checkApp :: (VarC v, Monad m)
         => Maybe (TmRef v) -> TmRef v -> [TmRef v] -> TyMonadT v m (TmRef v)
checkApp _  ty [] = return ty
checkApp tm tyt₁ (t₂ : ts) =
    do tyt₁' <- whnfM tyt₁
       case tyt₁' of
           Arr ty₁ s -> do tyCheck t₂ ty₁
                           ty <- constrIfTy (instantiate1 t₂ s)
                           checkApp Nothing ty ts
           _         -> expectingFunction tm tyt₁

constrIfTy :: (VarC v, Monad m) => TmRef v -> KMonadE f v m (Tm Ref v)
constrIfTy ty =
    do ty' <- whnfM ty
       case ty' of
           Ty r -> Ty <$> addConstr' (r :<=:)
           _    -> return ty

tyCheck :: (VarC v, Monad m) => TmRef v -> TmRef v -> TyMonadT v m ()
tyCheck = whnf₂ go
  where
    -- TODO try to iteratively get the whnf, instead the nf at once
    go :: (VarC v, Monad m) => TmRef v -> TmRef v -> TyMonadT v m ()
    go (Lam s₁) (Arr ty s₂) = nestM (P ty) (whnf₂ go (fromScope s₁) (fromScope s₂))
    go (Hole hn ts) ty =
        do tys <- mapM tyInfer' ts
           addHole =<< formHoleM hn ty (zip ts tys)
    go t ty =
        do tyt <- whnfM =<< tyInfer' t
           eq <- fromKMonadP (eqRefs ty tyt)
           unless eq (mismatch ty t tyt)

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
eqRefs (Data d₁ ts₁) (Data d₂ ts₂) =
    ((d₁ == d₂ &&) . and) <$> mapM (uncurry eqRefs) (zip ts₁ ts₂)
eqRefs (Hole x _) (Hole y _) = return (x == y)
eqRefs _ _ = return False

eqRefs' :: (VarC v, Monad m) => TmRef v -> TmRef v -> TyMonadP v m Bool
eqRefs' = whnf₂ eqRefs

isProp :: (VarC v, Monad m) => TmRef v -> TmRef v -> TyMonadT v m Bool
isProp t₀ (Ty _) = whnf₁ go t₀
  where
    go :: (VarC v, Monad m) => TmRef v -> TyMonadT v m Bool
    go (Arr ty s) = nestM (P ty) (whnf₁ go (fromScope s))
    go (appV -> (t, pars)) =
        do t' <- whnfM t
           case t' of
               V v -> (&&) <$> isRecM v <*> (and <$> mapM (whnf₁ go) pars)
               _   -> return False
isProp _ _ = return False

whnf₂ :: (Monad m, VarC v) => (TmRef v -> TmRef v -> TyMonad f v m a)
      -> TmRef v -> TmRef v -> TyMonad f v m a
whnf₂ m t₁ t₂ = join (m <$> whnfM t₁ <*> whnfM t₂)
whnf₁ :: (Monad m, VarC v) => (TmRef v -> TyMonad f v m a)
      -> TmRef v -> TyMonad f v m a
whnf₁ m t = m =<< whnfM t

simplify :: ProbRef -> Problem v -> [Problem v] -> TyMonadT v m ()
simplify = undefined

unify :: (VarC v, Monad m) => ProbRef -> Equation v -> TyMonadT v m ()
unify n q@(Eqn (Arr a b) f (Arr s t) g) =
    do let x        = B dummyN
           (xl, xr) = (V (Twin x TwinL), V (Twin x TwinR))
       eqn <- fromKMonadP $ nestPM $
              Eqn <$> whnfM (fromScope b) <*> whnfM (App (F <$> f) xl)
                  <*> whnfM (fromScope t) <*> whnfM (App (F <$> g) xr)
       r <- freshRef
       simplify n (Unify q)
                [Unify (Eqn (Ty r) a (Ty r) s), All (Twins a s) (Unify eqn)]
