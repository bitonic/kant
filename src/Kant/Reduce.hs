{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.Reduce (nf, whnf) where

import           Bound
import           Data.Proxy

import           Kant.ADT
import           Kant.Cursor
import           Kant.Env
import           Kant.Term
#include "../impossible.h"

type Reducer = forall v. VarC v => EnvP v -> TmRef v -> TmRef v


reduce :: Reducer -> Reducer
reduce r env t@(V v) =
    maybe t (reduce r env) (envBody env v)
reduce _ _ (Ty r) = (Ty r)
reduce r env (Lam s)    = Lam (reduceScope r env s)
reduce r env (Arr ty s) = Arr (r env ty) (reduceScope r env s)
reduce r env (Con ar tyc dc ts) = Con ar tyc dc (map (r env) ts)
reduce r env (Ann _ t) = reduce r env t
reduce r env (Hole hn ts) = Hole hn (map (reduce r env) ts)
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
reduce _ _ (Destr _ _ _ _) = IMPOSSIBLE("See first clause")

reduceScope :: VarC v => Reducer -> EnvP v -> TmScopeRef v -> TmScopeRef v
reduceScope r env s = (toScope (r (nestC env Proxy) (fromScope s)))

whnf :: VarC v => Env f v -> TmRef v -> TmRef v
whnf env = reduce (\_ t -> t) (toP env)

nf :: VarC v => Env f v -> TmRef v -> TmRef v
nf env = reduce nf (toP env)
