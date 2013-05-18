{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}
module Kant.Distill (distill) where

import           Control.Arrow (second)

import           Bound

import           Kant.Cursor
import           Kant.Elaborate
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
distill' (Data _ n TyCon ts)         = sapp (SPrim n : map distill' ts)
distill' (Data _ _ (DataCon dc) ts)  = sapp (SPrim dc : map distill' ts)
distill' (Rewr tyc (Elim ts))        = sapp (SPrim (elimName tyc) : map distill' ts)
distill' (Rewr _ (Proj n t))         = sapp [SPrim n, distill' t]
distill' (Ann ty t) = SAnn (map (second distill) pars) (distill ty') (distill t')
  where (pars, ty', t') = unrollAnn ty t
distill' (Hole hn ts) = SHole hn (map distill ts)

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
