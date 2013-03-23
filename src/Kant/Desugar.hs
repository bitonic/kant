{-# LANGUAGE TypeFamilies #-}
module Kant.Desugar (Desugar(..)) where

import           Control.Arrow (first, second)

import           Kant.Term
import           Kant.Decl
import           Kant.Sugar

class Desugar a where
    type Core a :: *
    desugar :: a -> Core a

instance Desugar STerm where
    type Core STerm = TermId

    desugar (SV n) = V n
    desugar STy = Ty
    desugar (SLam [] t) = desugar t
    desugar (SLam (vn : vs) t) = lam vn (desugar (SLam vs t))
    desugar (SArr [] t) = desugar t
    desugar (SArr ((vn, ty₁) : pars) ty₂) =
        arr vn (desugar ty₁) (desugar (SArr pars ty₂))
    desugar (SApp t₁ t₂) = App (desugar t₁) (desugar t₂)
    desugar (SAnn pars ty t) =
        Ann (desugar (SArr pars ty)) (desugar (SLam (map fst pars) t))
    desugar (SHole hn ts) = Hole hn (map desugar ts)

instance Desugar SDecl where
    type Core SDecl = Decl

    desugar (SVal n pars ty t) =
        Val n (desugar (SAnn pars ty t))
    desugar (SPostulate n t) = Postulate n (desugar t)
    desugar (SData c pars cons) =
        -- Add the parameters to each constructor
        Data c (desugar (SArr pars' STy)) (map (second (desugar . SArr pars')) cons)
      where pars' = (map (first Just) pars)

instance Desugar SModule where
    type Core SModule = Module
    desugar (SModule decls) = Module (map desugar decls)
