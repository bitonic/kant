{-# LANGUAGE RankNTypes #-}
module Kant.Reduce
    ( Reducer
    , nf
    , nf'
    , whnf
    , whnf'
    , defeq
    ) where

import           Data.Maybe (fromMaybe)
import           Data.Function (on)

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
reduce _ env t@(Var v) = fromMaybe t (lookupDef v env)
reduce _ _ (Type l) = Type l
reduce r env (App t₁ t₂) =
    case reduce r env t₁ of
        Lam _ s -> reduce r env (instantiate1 t₂ s)
        t₁'     -> App (r env t₁') (r env t₂)
reduce r env (Case t brs) =
    case unrollApp t' of
        (Var v, ts) ->
            case [ s | (n, i, s) <- brs, v == envNest env n, length ts == i ] of
                []      -> stuck
                (s : _) -> instantiateList ts s
        _ -> stuck
  where
    t'    = reduce r env t
    stuck = Case t' [ (n, i, reduceScope r env s) | (n, i, s) <- brs ]
reduce r env (Lam t s) =
    Lam (reduce r env t) (reduceScope r env s)

reduceScope :: (Eq b, Eq a)
            => Reducer -> EnvT a -> TScopeT a b -> TScopeT a b
reduceScope r env = toScope . reduce r (nestEnv env Nothing) . fromScope

-- | Reduces a term to its normal form - computes under binders, if you only
--   want canonical constructors see 'whnf'.
nf :: Reducer
nf = reduce nf

-- | Same as 'nf' but for closed 'Term's.
nf' :: Env -> Term -> Term
nf' env = nf env

whnf :: Reducer
whnf = reduce (\_ t -> t)

whnf' :: Env -> Term -> Term
whnf' env = whnf env

-- TODO eta expansion, congruence, blah blah.
-- | Definitional equality: reduce two terms to their normal forms, and then
--   check if they are equal.
defeq :: Eq a => EnvT a -> TermT a -> TermT a -> Bool
defeq env = (==) `on` nf env
