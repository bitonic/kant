{-# LANGUAGE ViewPatterns #-}
module Kant.Reduce
    ( Reducer
    , nf
    , whnf
    ) where

import           Control.Arrow (second)

import           Kant.Term
import           Kant.Environment

type Reducer = Env -> Term -> Term

addJustVal :: Env -> Binder Tag -> Term -> Env
addJustVal env Wild      _ = env
addJustVal env (Bind ta) t =
    -- We assert that the env does not contain that name yet
    let Just env' = addCtx env (Bound "" ta) (t, Nothing) in env'

addJustVals :: Env -> [(Binder Tag, Term)] -> Env
addJustVals = foldr (\(b, t) env -> addJustVal env b t)

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
        Lam b _ t -> reduce r (addJustVal env b t) t
        t₁'@(unrollApp -> (ft@(Fix b pars _ t), args)) ->
            -- TODO check that all this works with whnf, for example check that
            -- we don't have to normalise fty and fss manually.
            let t₂'           = reduce r env t₂
                args'         = args ++ [t₂']
                i             = length pars
                (fargs, rest) = splitAt i args'
                t'            = case b of
                                    Wild    -> t
                                    Bind ta -> subst' ta ft t
            in if i > length args' || not (all constr fargs)
               then App t₁' t₂'
               else app (reduce r (addJustVals env (zip (map fst pars) fargs)) t' :
                         rest)
        t₁'     -> App t₁' (r env t₂)
reduce r env (Case b t ty brs) =
    case t₁ of
        Constr c _ ts ->
            case [(bs, t₂) | (c', bs, t₂) <- brs, c == c', length ts == length bs] of
                []             -> stuck
                ((bs, t₂) : _) -> reduce r (addJustVals env (zip bs ts)) t₂
        _ -> stuck
  where
    t₁    = reduce r env t
    stuck = Case b t₁ (r env ty) [(c, bs, r env t₂) | (c, bs, t₂) <- brs ]
reduce r env (Lam b ty t) = Lam b (r env ty) (r env t)
reduce r env (Arr b ty₁ ty₂) = Arr b (r env ty₁) (r env ty₂)
reduce r env (Constr c tys ts) = Constr c (map (r env) tys) (map (r env) ts)
reduce r env (Fix b pars ty t) =
    Fix b (map (second (r env)) pars) (r env ty) (r env t)

constr :: TermT f t -> Bool
constr (Constr _ _ _) = True
constr _              = False

-- | Reduces a term to its normal form - computes under binders, if you only
--   want canonical constructors see 'whnf'.
nf :: Reducer
nf = reduce nf

-- | Reduces to weak head normal form: that is, does not reduce under binders.
whnf :: Reducer
whnf = reduce (\_ t -> t)
