{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.Reduce
    ( Reducer
    , nf
    , whnf
    ) where

import           Prelude hiding ((!!), length, splitAt)

import           Bound
import           Numeric.Natural

import           Kant.Common
import           Kant.Term
import           Kant.Environment

-- TODO remove the Show when we're not debugging anymore...
type Reducer = forall a. (Show a, Eq a) => EnvT a -> TermT a -> TermT a

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
        t₁'@(unrollApp -> (ft@(Fix _ (FixT i fss)), args)) ->
            -- TODO check that all this works with whnf, for example check that
            -- we don't have to normalise fty and fss manually.
            let t₂'           = reduce r env t₂
                args'         = args ++ [t₂']
                (fargs, rest) = splitAt i args'
            in if i > length args' || not (all constr fargs)
               then App t₁' t₂'
               else reduce r env (app (instantiateNatU fargs ft fss : rest))
        t₁'     -> App t₁' (r env t₂)
reduce r env (Case t (CaseT ty brs)) =
    case t' of
        Constr c _ ts ->
            case [ss | BranchT c' i ss <- brs, c == c', length ts == i] of
                []       -> stuck
                (ss : _) -> reduce r env (instantiateNatU ts t' ss)
        _ -> stuck
  where
    t'    = reduce r env t
    stuck = Case t' (CaseT (reduceScope r env ty)
                           [ BranchT c i (reduceScope² r env ss)
                           | BranchT c i ss <- brs ])
reduce r env (Lam t s) =
    Lam (reduce r env t) (reduceScope r env s)
reduce r env (Arr ty s) = Arr (r env ty) (reduceScope r env s)
reduce r env (Constr c pars ts) = Constr c (map (r env) pars) (map (r env) ts)
reduce r env (Fix ty (FixT i ss)) = Fix (r env ty) (FixT i (reduceScope² r env ss))

constr :: TermT a -> Bool
constr (Constr _ _ _) = True
constr _              = False

nestNothing :: EnvT a -> EnvT (Var (TName b) a)
nestNothing env = nestEnv env (const Nothing)

type TScopeNatU a = Scope (TName Natural) (Scope (TName ()) TermT) a

reduceScope :: (Eq a, Show a)
            => Reducer -> EnvT a -> TScope a -> TScope a
reduceScope r env = toScope . reduce r (nestNothing env) . fromScope

reduceScope² :: (Eq a, Show a)
             => Reducer -> EnvT a -> TScopeNatU a -> TScopeNatU a
reduceScope² r env = toScope . toScope . reduce r (nestNothing (nestNothing env)) .
                     fromScope . fromScope

-- | Reduces a term to its normal form - computes under binders, if you only
--   want canonical constructors see 'whnf'.
nf :: Reducer
nf = reduce nf

-- | Reduces to weak head normal form: that is, does not reduce under binders.
whnf :: Reducer
whnf = reduce (\_ t -> t)
