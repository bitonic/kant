module Kant.Distill (distill) where

import           Control.Arrow (second)

import           Bound

import           Kant.Sugar
import           Kant.Term
import           Kant.Uniquify
import           Kant.Env

distill :: TermId r -> STerm
distill = distill' . slam newEnv

distill' :: TermId r -> STerm
distill' (V v) = SV v
distill' (Ty _) = STy
distill' t₁@(Lam _) = SLam vs (distill' t₂)
  where (vs, t₂) = unrollLam t₁
distill' t₁@(Arr _ _) = SArr (map (second distill) pars) (distill' t₂)
  where (pars, t₂) = unrollArr t₁
distill' (App t₁ t₂) = SApp (distill' t₁) (distill' t₂)
distill' (Canon c ts) = distill' (app (V c : ts))
distill' (Elim ce ts) = distill' (app (V (ce) : ts))
distill' (Ann ty t) = SAnn (map (second distill) pars) (distill ty') (distill t')
  where (pars, ty', t') = unrollAnn ty t
distill' (Hole hn ts) = SHole hn (map distill ts)

unrollArr :: TermId r -> ([(Maybe Id, TermId r)], TermId r)
unrollArr (Arr ty s) = ((n, ty) : pars, t₂)
  where (n, t₁) = scopeN s; (pars, t₂) = unrollArr t₁
unrollArr t = ([], t)

unrollLam :: TermId r -> ([Maybe Id], TermId r)
unrollLam (Lam s) = (vn : vs, t₂)
  where (vn, t₁) = scopeN s; (vs, t₂) = unrollLam t₁
unrollLam t = ([], t)

unrollAnn :: TermId r -> TermId r -> ([(Maybe Id, TermId r)], TermId r, TermId r)
unrollAnn (Arr ty₁ s₁) (Lam s₂) = ((vn₂, ty₁) : pars, ty, t')
  where (vn₁, ty₂) = scopeN s₁
        (vn₂, t) = case vn₁ of
                       Nothing -> scopeN s₂
                       Just v  -> (Just v, instantiate1 (V v) s₂)
        (pars, ty, t') = unrollAnn ty₂ t
unrollAnn ty t = ([], ty, t)