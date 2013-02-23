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

type Reducer f = forall m. (Monad m, Functor m) => f Tag -> EnvM m (f Tag)

substB :: (Eq v, Subst f) => Binder t v -> TermT v -> f v -> f v
substB Wild _ t = t
substB (Bind _ v) t t' = substV v t t'

class Subst f => Reduce f where
    reduce :: (forall g. Reduce g => Reducer g) -> Reducer f

instance (Reduce f, Subst f) => Reduce (ScopeFT f) where
    reduce r (Scope b t) = Scope b <$> r t

instance (Reduce f, Subst f) => Reduce (BranchFT f) where
    reduce r (Branch brs t) = Branch brs <$> r t

instance (Reduce f, Subst f) => Reduce (ParamsFT f) where
    reduce r (ParamsT pars t) = ParamsT <$> sequence [(b,) <$> r ty | (b, ty) <- pars]
                                        <*> r t

instance Reduce FixT where
    reduce r (FixT t s) = FixT <$> r t <*> r s

instance Reduce TermT where
    reduce _ t@(Var v) = do tm <- envDef v; return (fromMaybe t tm)
    reduce _ t@(Type _) = return t
    reduce r (App t₁ t₂) =
        do t₁' <- reduce r t₁
           case t₁' of
               Lam _ (Scope b t) -> reduce r (substB b t₂ t)
               (unrollApp -> (ft@(Fix (ParamsT pars (FixT _ (Scope b t)))), args)) ->
                   do t₂' <- reduce r t₂
                      let args'         = args ++ [t₂']
                          i             = length pars
                          (fargs, rest) = splitAt i args'
                          t'            = substB b ft t
                      return $
                          if i > length args' || not (all constr fargs)
                          then App t₁' t₂'
                          else app (substPars (zip (map fst pars) args) t' : rest)
               _ -> return t₁'
    reduce r (Case t s brs) =
        do t₁ <- reduce r t
           stuck <- Case t₁ <$> r s <*> sequence [(c,) <$> r br | (c, br) <- brs]
           case t₁ of
               Constr c _ ts ->
                   case [ (bs, t₂) | (c', (Branch bs t₂)) <- brs, c == c',
                          length ts == length bs ]
                    of  []             -> return stuck
                        ((bs, t₂) : _) -> reduce r (substPars (zip bs ts) t₂)
               _ -> return stuck
    reduce r (Lam ty s) = Lam <$> r ty <*> r s
    reduce r (Arr ty s) = Arr <$> r ty <*> r s
    reduce r (Constr c tys ts) = Constr c <$> mapM r tys <*> mapM r ts
    reduce r (Fix pars) = Fix <$> r pars

substPars :: Subst f => [(TBinder, Term)] -> f Tag -> f Tag
substPars [] t = t
substPars ((Wild, _) : pars) t = substPars pars t
substPars ((Bind _ v, t) : pars) t' = substPars pars t''
  where Branch _ t'' = substV v t (Branch (map fst pars) t')

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

