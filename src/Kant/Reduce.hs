{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.Reduce (nf, whnf) where

import           Bound
import           Data.Proxy

import           Kant.ADT
import           Kant.Cursor
import           Kant.Env
import           Kant.Term

type Reducer = forall v. VarC v => EnvP v -> TmRef v -> TmRef v

reduce :: Reducer -> Reducer
reduce r env t@(V (getV -> v)) =
    maybe t (reduce r env) (envBody env v)
reduce _ _ (Ty r) = (Ty r)
reduce r env (Lam s)    = Lam (reduceScope r env s)
reduce r env (Arr ty s) = Arr (r env ty) (reduceScope r env s)
reduce r env (App t₁ t₂) =
    case reduce r env t₁ of
        Lam s -> reduce r env (instantiate1 t₂ s)
        t₁'   -> App t₁' (reduce r env t₂)
reduce r env (Rewr c (Elim ts)) =
    case adtRewr (envADT env c) ts' of
        Nothing -> Rewr c (Elim ts')
        Just t  -> reduce r env t
  where ts' = map (reduce r env) ts
reduce r env (Rewr c (Proj n t)) =
    case recRewr (envRec env c) n [t'] of
        Nothing  -> Rewr c (Proj n t')
        Just t'' -> reduce r env t''
  where t' = reduce r env t
reduce r env (Data ar c ct ts) = Data ar c ct (map (reduce r env) ts)
reduce r env (Ann _ t) = reduce r env t
reduce r env (Hole hn ts) = Hole hn (map (reduce r env) ts)

reduceScope :: VarC v => Reducer -> EnvP v -> TmScopeRef v -> TmScopeRef v
reduceScope r env s = (toScope (r (nestC env Proxy) (fromScope s)))

whnf :: VarC v => Env f v -> TmRef v -> TmRef v
whnf env = reduce (\_ t -> t) (toP env)

nf :: VarC v => Env f v -> TmRef v -> TmRef v
nf env = reduce nf (toP env)
