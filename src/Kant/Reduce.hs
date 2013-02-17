{-# LANGUAGE RankNTypes #-}
module Kant.Reduce
    ( Reducer
    , nf
    , whnf
    ) where

import           Bound

import           Kant.Term
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
    case t' of
        Constr c _ ts ->
            case [ss | (c', i, ss) <- brs, c == c', length ts == i] of
                [] -> stuck
                (ss : _) -> instantiate1 t'
                            (instantiateList (map (toScope . fmap F) ts) ss)
        _ -> stuck
  where
    t'    = reduce r env t
    stuck = Case t' (reduceScope r env ty)
                 [(c, i, reduceScope² r env ss) | (c, i, ss) <- brs]
reduce r env (Lam t s) =
    Lam (reduce r env t) (reduceScope r env s)
reduce r env (Arr ty s) = Arr (r env ty) (reduceScope r env s)
reduce r env (Constr c pars ts) = Constr c (map (r env) pars) (map (r env) ts)

nestNothing :: EnvT a -> EnvT (Var (TName b) a)
nestNothing env = nestEnv env (const Nothing)

reduceScope :: (Eq b, Eq a)
            => Reducer -> EnvT a -> TScopeT b a -> TScopeT b a
reduceScope r env = toScope . reduce r (nestNothing env) . fromScope

reduceScope² :: (Eq b, Eq c, Eq a)
             => Reducer -> EnvT a -> TScopeT² b c a -> TScopeT² b c a
reduceScope² r env = toScope . toScope . reduce r (nestNothing (nestNothing env)) .
                     fromScope . fromScope

-- | Reduces a term to its normal form - computes under binders, if you only
--   want canonical constructors see 'whnf'.
nf :: Reducer
nf = reduce nf

-- | Reduces to weak head normal form: that is, does not reduce under binders.
whnf :: Reducer
whnf = reduce (\_ t -> t)
