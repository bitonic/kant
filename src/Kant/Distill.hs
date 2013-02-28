module Kant.Distill (distillT) where

import           Kant.Sugar
import           Kant.Term

distillT :: TermId -> STerm
distillT (V v) = SV v
distillT (Ty l) = STy l
distillT (Lam ab) = undefined
distillT (Arr ab) = undefined
distillT (App t₁ t₂) = SApp (distillT t₁) (distillT t₂)
