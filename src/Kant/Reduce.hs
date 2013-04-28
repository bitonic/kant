{-# LANGUAGE RankNTypes #-}
module Kant.Reduce (nf, whnf) where

import           Bound
import           Data.Proxy

import           Kant.ADT
import           Kant.Cursor
import           Kant.Env
import           Kant.Term

type Reducer = forall v. VarC v => EnvP v -> TermRef v -> TermRef v

reduce :: Reducer -> Reducer
reduce r env t@(V v) =
    maybe t (reduce r env) (envBody env v)
reduce _ _ (Ty r) = (Ty r)
reduce r env (Lam s)    = Lam (reduceScope r env s)
reduce r env (Arr ty s) = Arr (r env ty) (reduceScope r env s)
reduce r env (App t₁ t₂) =
    case reduce r env t₁ of
        Lam s -> reduce r env (instantiate1 t₂ s)
        t₁'   -> App t₁' (reduce r env t₂)
reduce r env (Canon c ts) = Canon c (map (reduce r env) ts)
reduce r env (Rewr c ts) =
    case adtRewr (envADT env c) ts' of
         Nothing -> Rewr c ts'
         Just t  -> reduce r env t
  where ts' = map (reduce r env) ts
reduce r env (Ann _ t) = reduce r env t
reduce r env (Hole hn ts) = Hole hn (map (reduce r env) ts)

reduceScope :: VarC v => Reducer -> EnvP v -> TermScopeRef v -> TermScopeRef v
reduceScope r env s = (toScope (r (nestC env Proxy) (fromScope s)))

whnf :: VarC v => Env f v -> TermRef v -> TermRef v
whnf env = reduce (\_ t -> t) (toP env)

nf :: VarC v => Env f v -> TermRef v -> TermRef v
nf env = reduce nf (toP env)
