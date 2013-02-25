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
import           Data.Maybe (fromMaybe)

import           Kant.Term
import           Kant.Environment

type Reducer f = forall m. MonadEnv m => f TName -> m (f TName)

class Bound f => Reduce f where
    reduce :: (forall g. Reduce g => Reducer g) -> Reducer f

instance (Reduce f) => Reduce (ScopeFT f) where
    reduce r (Scope b t) = Scope b <$> r t

instance (Reduce f, Reduce g) => Reduce (TelePFT g f) where
    reduce r (Tele pars t) = Tele <$> sequence [(b,) <$> r ty | (b, ty) <- pars]
                                  <*> r t
instance Reduce FixT where
    reduce r (FixT t s) = FixT <$> r t <*> r s

instance Reduce Proxy where
    reduce _ Proxy = return Proxy

instance Reduce TermT where
    reduce _ t@(Var v) = -- TODO should I reduce here?
                         do tm <- envDef v; return (fromMaybe t tm)
    reduce _ t@(Type _) = return t
    reduce r (App t₁ t₂) =
        do t₁' <- reduce r t₁
           case t₁' of
               Lam _ (Scope b t) -> reduce r =<< subst b t₂ t
               (unrollApp -> (ft@(Fix te@(Tele pars _)), args)) ->
                   do t₂' <- reduce r t₂
                      let args'         = args ++ [t₂']
                          i             = length pars
                          (fargs, rest) = splitAt i args'
                      if i > length args' || not (all constr fargs)
                        then return (App t₁' t₂')
                        else do FixT _ (Scope b t') <- substTele te fargs
                                t'' <- subst b ft t'
                                reduce r (app (t'' : rest))
               _ -> App t₁' <$> reduce r t₂
    reduce r (Case t s brs) =
        do t₁ <- reduce r t
           stuck <- Case t₁ <$> r s <*> sequence [(c,) <$> r br | (c, br) <- brs]
           case t₁ of
               Constr c _ ts ->
                   case [ br | (c', br@(Tele (branchBs -> bs) _)) <- brs, c == c',
                          length ts == length bs ]
                    of  []         -> return stuck
                        (br : _) -> reduce r =<< substBranch br ts
               _ -> return stuck
    reduce r (Lam ty s) = Lam <$> r ty <*> r s
    reduce r (Arr ty s) = Arr <$> r ty <*> r s
    reduce r (Constr c tys ts) = Constr c <$> mapM r tys <*> mapM r ts
    reduce r (Fix pars) = Fix <$> r pars

constr :: TermT v -> Bool
constr (Constr _ _ _) = True
constr _              = False

-- | Reduces a term to its normal form - computes under binders, if you only
--   want canonical constructors see 'whnf'.
nf :: Reduce f => Reducer f
nf = reduce nf

-- -- | Reduces to weak head normal form: that is, does not reduce under binders.
whnf :: Reduce f => Reducer f
whnf = reduce return
