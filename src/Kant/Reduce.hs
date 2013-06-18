{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
-- | Functions that... reduce terms.
module Kant.Reduce (nf, whnf, nf', whnf') where

import           Bound
import           Data.Proxy

import           Kant.ADT
import           Kant.Cursor
import           Kant.Env
import           Kant.Term
#include "../impossible.h"

import Debug.Trace

type Reducer = forall v. VarC v => Bool -> EnvP v -> TmRef v -> TmRef v

-- TODO Do I need to reduce proofs?  I probably shouldn't.

reduce :: Reducer -> Reducer
reduce r True env t@(V v) =
    maybe t (reduce r True env) (envBody env v)
reduce _ False _ t@(V _) = t
reduce _ _ _ (Ty r) = (Ty r)
reduce r i env (Lam s)    = Lam (reduceScope r i env s)
reduce r i env (Arr ty s) = Arr (reduce r i env ty) (reduceScope r i env s)
reduce r i env (Con ar tyc dc ts) = Con ar tyc dc (map (reduce r i env) ts)
reduce r i env (Ann _ t) = reduce r i env t
reduce r i env (Hole hn ts) = Hole hn (map (reduce r i env) ts)
reduce r i env (Eq t₁ ty₁ t₂ ty₂) =
    reduceEq r env (reduce r i env t₁) (reduce r i env ty₁)
                   (reduce r i env t₂) (reduce r i env ty₂)
reduce r i env (Coeh Coe ty₁ ty₂ t p) =
    reduceCoe r env (reduce r i env ty₁) (reduce r i env ty₂)
                    (reduce r i env t) (reduce r i env p)
reduce r i env (Coeh Coh ty₁ ty₂ t p) =
    Coeh Coh (reduce r i env ty₁) (reduce r i env ty₂)
             (reduce r i env t) (reduce r i env p)
reduce _ _ _ (Prop r) = Prop r
reduce _ _ _ Top = Top
reduce _ _ _ Bot = Bot
reduce r i env (And pr₁ pr₂) = And (reduce r i env pr₁) (reduce r i env pr₂)
reduce r i env (Forall ty s) = Forall (reduce r i env ty) (reduceScope r i env s)
reduce r i env (Dec pr) = reduceDec r env (reduce r i env pr)
-- TODO I think that matching here directly on 'Destr' without reducing first is
-- safe, but I'm not sure, check.
reduce r i env (appV -> (Destr ar tyc n t, ts)) =
    case ar of
        ADT_ -> case adtRewr (envADT env tyc) t' ts of
                    Nothing  -> stuck
                    Just ts' -> reduce r i env (app ts')
        Rec_ -> case recRewr (envRec env tyc) n t' ts of
                    Nothing  -> stuck
                    Just ts' -> reduce r i env (app ts')
  where
    t'    = reduce r i env t
    stuck = app (Destr ar tyc n t' : map (reduce r i env) ts)
reduce r i env (App t₁ t₂) =
    case reduce r i env t₁ of
        Lam s -> reduce r i env (instantiate1 t₂ s)
        t₁'   -> App t₁' (reduce r i env t₂)

reduce _ _ _ (Destr _ _ _ _) = IMPOSSIBLE("See previous clauses")

-- reduceTyEq :: VarC v => Reducer -> EnvP v -> TmRef v -> TmRef v -> TmRef v
-- reduceTyEq r env (Arr ty₁ s₁) (Arr ty₂ s₂) =
--     reduce r env $
--     P.and env (TyEq ty₂ ty₁)
--               (Arr ty₂ (toScope (Arr (F <$> ty₁) (toScope (reduce r env₂ q)))))
--   where
--     x₂   = V (F (B dummyN))
--     x₁   = V (B dummyN)
--     env₂ = nestC (nestC env (const Proxy)) (const Proxy)
--     q    = TyEq (instantiate1 x₁ (F . F <$> s₁)) (instantiate1 x₂ (F . F <$> s₂))
-- reduceTyEq r env (appV -> (V v₁, ts₁)) (appV -> (V v₂, ts₂)) =
--     undefined
-- reduceTyEq _ _ ty₁ ty₂ = TyEq ty₁ ty₂

reduceEq :: VarC v => Reducer -> EnvP v
         -> TmRef v -> TmRef v -> TmRef v -> TmRef v -> TmRef v
reduceEq = undefined

reduceDec :: VarC v => Reducer -> EnvP v -> TmRef v -> TmRef v
reduceDec = undefined

reduceCoe :: VarC v => Reducer -> EnvP v
          -> TmRef v -> TmRef v -> TmRef v -> TmRef v -> TmRef v
reduceCoe = undefined

reduceScope :: VarC v => Reducer -> Bool -> EnvP v -> TmScopeRef v -> TmScopeRef v
reduceScope r i env s = toScope (r i (nestC env (const Proxy)) (fromScope s))

-- | Reduce to "weak head normal form".
whnf :: VarC v => Env f v -> TmRef v -> TmRef v
whnf env = reduce (\_ _ t -> t) True (toP env)

-- | Reduce to full normal form.
nf :: VarC v => Env f v -> TmRef v -> TmRef v
nf env = reduce (\_ -> nf) True (toP env)

-- | Reduce to "weak head normal form".
whnf' :: VarC v => Env f v -> TmRef v -> TmRef v
whnf' env = reduce (\_ _ t -> t) False (toP env)

-- | Reduce to full normal form.
nf' :: VarC v => Env f v -> TmRef v -> TmRef v
nf' env = reduce (\_ -> nf') False (toP env)
