module Kant.Desugar (desugarT) where

import           Kant.Sugar
import           Kant.Term

desugarT :: STerm -> TermId
desugarT (SV n) = V n
desugarT STy = Ty
desugarT (SLam pars t) = desugarAb lam pars t
desugarT (SArr pars t) = desugarAb arr pars t
desugarT (SApp t₁ t₂) = App (desugarT t₁) (desugarT t₂)

desugarAb :: (String -> TermId -> TermId -> TermId)
          -> [(Maybe [String], STerm)] -> STerm -> TermId
desugarAb _ [] t = desugarT t
desugarAb f ((Nothing, ty) : pars) t = f "" (desugarT ty) (desugarAb f pars t)
desugarAb f ((Just [], _) : pars) t = desugarAb f pars t
desugarAb f ((Just (n : ns), ty) : pars) t =
    f n (desugarT ty) (desugarAb f ((Just ns, ty) : pars) t)
