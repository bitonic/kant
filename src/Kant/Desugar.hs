{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Kant.Desugar (Desugar(..)) where

import           Control.Arrow (second)

import           Kant.Term
import           Kant.Decl
import           Kant.Sugar

class Desugar a b where
    desugar :: a -> b

instance (a ~ TermId) => Desugar STerm a where
    desugar (SV n) = V n
    desugar STy = Ty
    desugar (SLam [] t) = desugar t
    desugar (SLam (vn : vs) t) = lam vn (desugar (SLam vs t))
    desugar (SArr [] t) = desugar t
    desugar (SArr ((vn, ty₁) : pars) ty₂) =
        arr vn (desugar ty₁) (desugar (SArr pars ty₂))
    desugar (SApp t₁ t₂) = App (desugar t₁) (desugar t₂)
    desugar (SAnn ty t) = Ann (desugar ty) (desugar t)

instance (a ~ Decl) => Desugar SDecl a where
    desugar (SVal n pars ty t) =
        Val n (desugar (SAnn (SArr pars ty) (SLam (map fst pars) t)))
    desugar (SPostulate n t) = Postulate n (desugar t)
    desugar (SData c pars cons) =
        Data c (desugar (SArr pars STy)) (map (second desugar) cons)

instance (a ~ Module) => Desugar SModule a where
    desugar (SModule decls) = Module (map desugar decls)
