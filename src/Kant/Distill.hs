module Kant.Distill (distillT) where

import           Control.Arrow (first, second)

import           Bound
import           Bound.Scope
import           Bound.Name

import           Kant.Sugar
import           Kant.Term

distillT :: TermId -> STerm
distillT (V v) = SV v
distillT (Ty l) = STy l
distillT t₁@(Lam _) = SLam (distillPars pars) (distillT t₂)
  where (pars, t₂) = first groupPars (unrollLam t₁)
distillT t₁@(Arr _) = SArr (distillPars pars) (distillT t₂)
  where (pars, t₂) = first groupPars (unrollArr t₁)
distillT (App t₁ t₂) = SApp (distillT t₁) (distillT t₂)

distillPars :: [(Maybe [Id], TermId)] -> [SParam]
distillPars = map (second distillT)

groupPars :: [(Maybe Id, TermId)] -> [(Maybe [Id], TermId)]
groupPars = map (first (fmap (:[])))

unrollLam :: TermId -> ([(Maybe Id, TermId)], TermId)
unrollLam (Lam (Abs ty s)) =
    ((n, ty) : pars, t₂)
  where (n, t₁) = scopeVar s; (pars, t₂) = unrollLam t₁
unrollLam t = ([], t)

unrollArr :: TermId -> ([(Maybe Id, TermId)], TermId)
unrollArr (Arr (Abs ty s)) =
    ((n, ty) : pars, t₂)
  where (n, t₁) = scopeVar s; (pars, t₂) = unrollArr t₁
unrollArr t = ([], t)

scopeVar :: Scope (NameId ()) Term Id -> (Maybe Id, TermId)
scopeVar s = case bindings s of
                 [] -> (Nothing, instantiate1 undefined s) -- Safe
                 (Name n _ : _) -> (Just n, instantiate1 (V n) s)
