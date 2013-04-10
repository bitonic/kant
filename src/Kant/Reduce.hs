{-# LANGUAGE RankNTypes #-}
module Kant.Reduce
    ( Reducer
    , nf
    , whnf
    ) where

import           Bound

import           Kant.Term
import           Kant.Env

type Reducer = forall v. Show v => Env v -> TermRef v -> TermRef v

reduce :: Reducer -> Reducer
reduce r env@Env{envValue = value} t@(V v) =
    maybe t (reduce r env) (value v)
reduce _ _ (Ty r) = (Ty r)
reduce r env (Lam s)    = Lam (reduceScope r env s)
reduce r env (Arr ty s) = Arr (r env ty) (reduceScope r env s)
reduce r env (App t₁ t₂) =
    case reduce r env t₁ of
        Lam s -> reduce r env (instantiate1 t₂ s)
        t₁'   -> App t₁' (reduce r env t₂)
reduce r env (Canon c ts) = Canon c (map (reduce r env) ts)
reduce r env (Elim c ts) =
    case envElim env c ts' of Nothing -> Elim c ts'; Just t  -> reduce r env t
  where ts' = map (reduce r env) ts
reduce r env (Ann _ t) = reduce r env t
reduce r env (Hole hn ts) = Hole hn (map (reduce r env) ts)

reduceScope :: forall v. Show v
            => Reducer -> Env v -> TermScope Ref v -> TermScope Ref v
reduceScope r env s = (toScope (r (nestEnv env Nothing Nothing) (fromScope s)))

whnf :: Reducer
whnf = reduce (\_ t -> t)

nf :: Reducer
nf = reduce nf
