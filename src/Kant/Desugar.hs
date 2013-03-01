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
    desugar (SLam pars t) = desugarAb lam pars t
    desugar (SArr pars t) = desugarAb arr pars t
    desugar (SApp t₁ t₂) = App (desugar t₁) (desugar t₂)

desugarAb :: (String -> TermId -> TermId -> TermId)
          -> [(Maybe [String], STerm)] -> STerm -> TermId
desugarAb _ [] t = desugar t
desugarAb f ((Nothing, ty) : pars) t = f "" (desugar ty) (desugarAb f pars t)
desugarAb f ((Just [], _) : pars) t = desugarAb f pars t
desugarAb f ((Just (n : ns), ty) : pars) t =
    f n (desugar ty) (desugarAb f ((Just ns, ty) : pars) t)

instance (a ~ Decl) => Desugar SDecl a where
    desugar (SVal n pars t) = Val n (desugar (SLam pars t))
    desugar (SPostulate n t) = Postulate n (desugar t)
    desugar (SData c pars cons) =
        Data c (desugar (SArr pars STy)) (map (second desugar) cons)
