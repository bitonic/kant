{-# LANGUAGE RankNTypes #-}
module Kant.Reduce
    ( Reducer
    , nf
    , whnf
    )
    where

import           Bound

import           Kant.Term
import           Kant.Env

type Reducer = forall v. Env v -> Term v -> Term v

reduce :: Reducer -> Reducer
reduce r env@Env{envValue = value} t@(V v) =
    maybe t (reduce r env) (value v)
reduce _ _ (Ty l) = Ty l
reduce r env (Lam ab) = Lam (reduceAb r env ab)
reduce r env (Arr ab) = Arr (reduceAb r env ab)
reduce r env (App t₁ t₂) =
    case reduce r env t₁ of
        Lam (Abs _ s) -> reduce r env (instantiate1 t₂ s)
        t₁'           -> App t₁' (reduce r env t₂)

reduceAb :: Reducer -> Env v -> Abs v -> Abs v
reduceAb r env (Abs t₁ t₂) =
    Abs (r env t₁) (toScope (r (nestEnv env Nothing Nothing) (fromScope t₂)))

whnf :: Reducer
whnf = reduce (\_ t -> t)

nf :: Reducer
nf = reduce nf
