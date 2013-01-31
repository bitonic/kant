{-# LANGUAGE RankNTypes #-}
module Kant.Reduce
    ( Reducer
    , EnvT
    , Env
    , Lift
    , nf
    , nf'
    , whnf
    , whnf'
    ) where

import           Control.Applicative ((<$>))

import           Bound

import           Kant.Syntax


type Lift a = ConId -> a
type EnvT a = a -> TermT a
type Env = EnvT Id

type Reducer = forall a. Eq a => EnvT a -> Lift a -> TermT a -> TermT a

-- TODO do something better, e.g. exceptions, when there are mismatches, for
-- example on 'case'.
-- | Reduces a term.  Assumes that the code is type checked.  For example it
--   doesn't do anything when the scrutined term under 'Case' doesn't match any
--   branch; and similarly doesn't complain when two branches can be taken, in
--   which case some matching will be taken.
reduce :: Reducer -> Reducer
reduce _ env _ (Var v) = env v
reduce _ _ _ (Type l) = Type l
reduce r env lif (App t₁ t₂) =
    case reduce r env lif t₁ of
        Lam _ s -> reduce r env lif (instantiate1 t₂ s)
        t₁'     -> App (r env lif t₁') (r env lif t₂)
reduce r env lif (Case t brs) =
    case unrollApp t' of
        (Var v, ts) ->
            case [ s | (n, i, s) <- brs, v == lif n, length ts == i ] of
                []      -> stuck
                (s : _) -> instantiateList ts s
        _ -> stuck
  where
    t'    = reduce r env lif t
    stuck = Case t' [ (n, i, reduceScope r env lif s) | (n, i, s) <- brs ]
reduce r env lif (Lam t s) =
    Lam (reduce r env lif t) (reduceScope r env lif s)

reduceScope :: (Eq b, Eq a)
            => Reducer -> EnvT a -> Lift a -> TScopeT a b -> TScopeT a b
reduceScope r env lif = toScope . uncurry r (extend env lif) . fromScope

unrollApp :: TermT a -> (TermT a, [TermT a])
unrollApp = go []
  where
    go ts (App t₁ t₂) = go (t₂ : ts) t₁
    go ts t           = (t, reverse ts)

extend :: EnvT a -> Lift a -> (EnvT (Var b a), Lift (Var b a))
extend env lif = (goenv, F . lif)
  where
    goenv v@(B _) = Var v
    goenv   (F v) = F <$> env v

-- | Reduces a term to its normal form - computes under binders, if you only
--   want canonical constructors see 'whnf'.
nf :: Reducer
nf = reduce nf

-- | Same as 'nf' but for closed 'Term's.
nf' :: Env -> Term -> Term
nf' env = nf env id

whnf :: Reducer
whnf = reduce (\_ _ t -> t)

whnf' :: Env -> Term -> Term
whnf' env = whnf env id
