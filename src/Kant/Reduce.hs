{-# LANGUAGE RankNTypes #-}
module Kant.Reduce
    ( Reducer
    , nf
    , whnf
    ) where

import           Bound

import           Kant.Syntax
import           Kant.Environment


type Reducer = forall a. Eq a => EnvT a -> TermT a -> TermT a

-- | Reduces a term.  Assumes that the code is type checked:
--
--   * It doesn't do anything when the scrutined term under 'Case' doesn't match
--     any branch; and similarly doesn't complain when two branches can be
--     taken, in which case some matching will be taken.
--
--   * When it encounters an out of bounds definition it simply leaves the
--     variable there.
reduce :: Reducer -> Reducer
reduce r env t@(Var v) = maybe t (r env) (envDef env v)
reduce _ _ (Type l) = Type l
reduce r env (App t₁ t₂) =
    case reduce r env t₁ of
        Lam _ s -> reduce r env (instantiate1 t₂ s)
        t₁'     -> App (r env t₁') (r env t₂)
reduce r env (Case t ty brs) =
    case unrollApp t' of
        (Var v, ts) ->
            case [ s | (n, i, s) <- brs, v == envNest env n, length ts == i ] of
                []      -> stuck
                (s : _) -> instantiateList ts s
        _ -> stuck
  where
    t'    = reduce r env t
    stuck = Case t' (r env ty) [(n, i, reduceScope r env s) | (n, i, s) <- brs]
reduce r env (Lam t s) =
    Lam (reduce r env t) (reduceScope r env s)

reduceScope :: (Eq b, Eq a)
            => Reducer -> EnvT a -> TScopeT a b -> TScopeT a b
reduceScope r env = toScope . reduce r (nestEnv env (const Nothing)) . fromScope

-- | Reduces a term to its normal form - computes under binders, if you only
--   want canonical constructors see 'whnf'.
nf :: Reducer
nf = reduce nf

-- | Reduces to weak head normal form: that is, does not reduce under binders.
whnf :: Reducer
whnf = reduce (\_ t -> t)
