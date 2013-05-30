{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
-- | Functions that... reduce terms.
module Kant.Reduce (nf, whnf) where

import           Bound
import           Data.Proxy

import           Kant.ADT
import           Kant.Common
import           Kant.Cursor
import           Kant.Env
import qualified Kant.Prelude as P
import           Kant.Term
#include "../impossible.h"

type Reducer = forall v. VarC v => EnvP v -> TmRef v -> TmRef v

reduce :: Reducer -> Reducer
reduce r env t@(V v) =
    maybe t (reduce r env) (envBody env v)
reduce _ _ (Ty r) = (Ty r)
reduce r env (Lam s)    = Lam (reduceScope r env s)
reduce r env (Arr ty s) = Arr (reduce r env ty) (reduceScope r env s)
reduce r env (Con ar tyc dc ts) = Con ar tyc dc (map (reduce r env) ts)
reduce r env (Ann _ t) = reduce r env t
reduce r env (Hole hn ts) = Hole hn (map (reduce r env) ts)
reduce r env (TyEq ty₁ ty₂) = reduceTyEq r env (reduce r env ty₁) (reduce r env ty₂)
reduce r env (HeEq t₁ ty₁ t₂ ty₂) =
    reduceHeEq r env (reduce r env t₁) (reduce r env ty₁)
                     (reduce r env t₂) (reduce r env ty₂)
-- TODO I think that matching here directly on 'Destr' without reducing first is
-- safe, but I'm not sure, check.
reduce r env (appV -> (Destr ar tyc n t, ts)) =
    case ar of
        ADT_ -> case adtRewr (envADT env tyc) t' ts of
                    Nothing  -> stuck
                    Just ts' -> reduce r env (app ts')
        Rec_ -> case recRewr (envRec env tyc) n t' ts of
                    Nothing  -> stuck
                    Just ts' -> reduce r env (app ts')
  where
    t'    = reduce r env t
    stuck = app (Destr ar tyc n t' : map (reduce r env) ts)
reduce r env (App t₁ t₂) =
    case reduce r env t₁ of
        Lam s -> reduce r env (instantiate1 t₂ s)
        t₁'   -> App t₁' (reduce r env t₂)
reduce _ _ (Destr _ _ _ _) = IMPOSSIBLE("See previous clauses")

reduceTyEq :: VarC v => Reducer -> EnvP v -> TmRef v -> TmRef v -> TmRef v
reduceTyEq r env (Arr ty₁ s₁) (Arr ty₂ s₂) =
    reduce r env $
    P.and env (TyEq ty₂ ty₁)
              (Arr ty₂ (toScope (Arr (F <$> ty₁) (toScope (reduce r env₂ q)))))
  where
    x₂   = V (F (B dummyN))
    x₁   = V (B dummyN)
    env₂ = nestC (nestC env (const Proxy)) (const Proxy)
    q    = TyEq (instantiate1 x₁ (F . F <$> s₁)) (instantiate1 x₂ (F . F <$> s₂))
reduceTyEq r env (appV -> (V v₁, ts₁)) (appV -> (V v₂, ts₂)) =
    undefined
reduceTyEq _ _ ty₁ ty₂ = TyEq ty₁ ty₂

reduceHeEq :: VarC v => Reducer -> EnvP v
           -> TmRef v -> TmRef v -> TmRef v -> TmRef v -> TmRef v
reduceHeEq = undefined

reduceScope :: VarC v => Reducer -> EnvP v -> TmScopeRef v -> TmScopeRef v
reduceScope r env s = toScope (r (nestC env (const Proxy)) (fromScope s))

-- | Reduce to "weak head normal form".
whnf :: VarC v => Env f v -> TmRef v -> TmRef v
whnf env = reduce (\_ t -> t) (toP env)

-- | Reduce to full normal form.
nf :: VarC v => Env f v -> TmRef v -> TmRef v
nf env = reduce nf (toP env)
