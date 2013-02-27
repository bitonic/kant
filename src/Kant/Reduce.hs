{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.Reduce
    ( Reduce(..)
    , Reducer
    , nf
    , whnf
    )
    where

import           Control.Applicative ((<$>), (<*>))

import           Kant.Term
import           Kant.Environment

type Reducer f = forall m. MonadSubst m => Env -> f TName -> m (f TName)

class Bound f => Reduce f where
    reduce :: (forall g. Reduce g => Reducer g) -> Reducer f

instance (Reduce f) => Reduce (ScopeFT f) where
    reduce r env (Scope b t) = Scope b <$> r env t

instance (Reduce f, Reduce g) => Reduce (TelePFT g f) where
    reduce r env (Tele pars t) =
        Tele <$> sequence [(b,) <$> r env ty | (b, ty) <- pars]
             <*> r env t
instance Reduce AbsT where
    reduce r env (Abs t s) = Abs <$> r env t <*> r env s

instance Reduce Proxy where
    reduce _ _ Proxy = return Proxy

instance Reduce TermT where
    -- TODO why does it loop if I reduce here?
    reduce _ env t@(Var v) = maybe (return t) return (envDef env v)
    reduce _ _ t@(Type _) = return t
    reduce r env (App t₁ t₂) =
        do t₁' <- reduce r env t₁
           case t₁' of
               Lam (Abs _ (Scope b t)) -> reduce r env =<< subst b t₂ t
               (unrollApp -> (ft@(Fix te@(Tele pars _)), args)) ->
                   do t₂' <- reduce r env t₂
                      let args'         = args ++ [t₂']
                          i             = length pars
                          (fargs, rest) = splitAt i args'
                      if i > length args' || not (all constr fargs)
                        then return (App t₁' t₂')
                        else do Abs _ (Scope b t') <- substTele te fargs
                                t'' <- subst b ft t'
                                reduce r env (app (t'' : rest))
               _ -> App t₁' <$> reduce r env t₂
    reduce r env (Case t s brs) =
        do t₁ <- reduce r env t
           stuck <- Case t₁ <$> r env s
                            <*> sequence [(c,) <$> r env br | (c, br) <- brs]
           case t₁ of
               Constr c _ ts ->
                   case [ br | (c', br@(Tele (branchBs -> bs) _)) <- brs, c == c',
                          length ts == length bs ]
                    of  []         -> return stuck
                        (br : _) -> reduce r env =<< substBranch br ts
               _ -> return stuck
    reduce r env (Lam ab) = Lam <$> r env ab
    reduce r env (Arr ab) = Arr <$> r env ab
    reduce r env (Constr c tys ts) = Constr c <$> mapM (r env) tys <*> mapM (r env) ts
    reduce r env (Fix pars) = Fix <$> r env pars

constr :: TermT v -> Bool
constr (Constr _ _ _) = True
constr _              = False

-- | Reduces a term to its normal form - computes under binders, if you only
--   want canonical constructors see 'whnf'.
nf :: Reduce f => Reducer f
nf = reduce nf

-- -- | Reduces to weak head normal form: that is, does not reduce under binders.
whnf :: Reduce f => Reducer f
whnf = reduce (\_ t -> return t)
