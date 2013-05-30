{-# LANGUAGE ViewPatterns #-}
-- | Transform 'Tm' back to a 'Sugar'.  We never need to handle 'Decl' or
--   'Modules', since everything is going to be elaborated.
module Kant.Distill (distill) where

import           Control.Arrow (second)

import           Bound

import           Kant.Cursor
import           Kant.Sugar
import           Kant.Term
import           Kant.Uniquify

distill :: TmId r -> STm r
distill = distill' . slam newCurs

distill' :: TmId r -> STm r
distill' (V v) = SV v
distill' (Ty r) = STy r
distill' t₁@(Lam _) = SLam vs (distill' t₂)
  where (vs, t₂) = unrollLam t₁
distill' t₁@(Arr _ _) = SArr (map (second distill) pars) (distill' t₂)
  where (pars, t₂) = unrollArr t₁
distill' (App t₁ t₂) = SApp (distill' t₁) (distill' t₂)
distill' (Con _ _ dc ts) = sapp (SV dc : map distill' ts)
distill' (Destr _ _ n t) = sapp [SV n, distill' t]
distill' (Ann ty t) = SAnn (map (second distill) pars) (distill ty') (distill t')
  where (pars, ty', t') = unrollAnn ty t
distill' (Hole hn ts) = SHole hn (map distill ts)
distill' (TyEq ty₁ ty₂) = STyEq (distill ty₁) (distill ty₂)
distill' (HeEq t₁ ty₁ t₂ ty₂) =
     SHeEq (distill t₁) (distill ty₁) (distill t₂) (distill ty₂)
distill' (Coe q t) = SCoe (distill q) (distill t)
distill' (Coh q t) = SCoh (distill q) (distill t)

sapp :: [STm r] -> STm r
sapp = foldl1 SApp

unrollArr :: TmId r -> ([(Maybe Id, TmId r)], TmId r)
unrollArr (Arr ty s) = ((n, ty) : pars, t₂)
  where (n, t₁) = scopeN s; (pars, t₂) = unrollArr t₁
unrollArr t = ([], t)

unrollLam :: TmId r -> ([Maybe Id], TmId r)
unrollLam (Lam s) = (vn : vs, t₂)
  where (vn, t₁) = scopeN s; (vs, t₂) = unrollLam t₁
unrollLam t = ([], t)

unrollAnn :: TmId r -> TmId r -> ([(Maybe Id, TmId r)], TmId r, TmId r)
unrollAnn (Arr ty₁ s₁) (Lam s₂) = ((vn₂, ty₁) : pars, ty, t')
  where (vn₁, ty₂) = scopeN s₁
        (vn₂, t) = case vn₁ of
                       Nothing -> scopeN s₂
                       Just v  -> (Just v, instantiate1 (V v) s₂)
        (pars, ty, t') = unrollAnn ty₂ t
unrollAnn ty t = ([], ty, t)
