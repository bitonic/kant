module Kant.Uniquify
    ( Uniquify(..)
    , UniqueM
    , Count
    ) where

import           Control.Applicative ((<$>), (<*>), (<$))

import           Control.Monad.State (State, MonadState(..))

import           Data.Void

import           Kant.Term

type Count = Integer

type UniqueM = State Count

class Uniquify f where
    uniquify :: f Void Id -> UniqueM (f Id Tag)

fresh :: State Count Tag
fresh = do ta <- get
           put (ta + 1)
           return (show ta)

freshBinder :: Binder Tag -> State Count (Binder Tag)
freshBinder b = (<$ b) <$> fresh

instance Uniquify TermT where
    uniquify (Var (Bound _ n))      = return (Var (Free n))
    uniquify (Var (Free v))         = absurd v
    uniquify (Type l)               = return (Type l)
    uniquify (App t₁ t₂)            = App <$> uniquify t₁ <*> uniquify t₂
    uniquify (Arr (Bind n) ty₁ ty₂) = undefined
        -- do ta <- fresh
        --    Arr (Bind ta) <$> uniquify (subst n (Var (Bound n ta))) <*> undefined

substTag :: Binder Tag -> Binder Tag -> TermV -> TermV
substTag Wild      _          t = t
substTag (Bind ta) (Bind ta') t = subst ta (\n -> Var (Bound n ta')) t
substTag _         _          _ = error "Uniquify.substTag': Binder mismatch"

substBrsTag :: Binder Tag -> Binder Tag -> [BranchV] -> [BranchV]
substBrsTag Wild      _          brs = brs
substBrsTag (Bind ta) (Bind ta') brs = substBrs ta (\n -> Var (Bound n ta')) brs
substBrsTag _         _          _   =
    error "Uniquify.substBrsTag: Binder mismatch"

substParsTag :: Binder Tag -> Binder Tag -> [ParamV] -> TermV -> ([ParamV], TermV)
substParsTag Wild       _         brs t = (brs, t)
substParsTag (Bind ta) (Bind ta') brs t = substPars ta (\n -> Var (Bound n ta')) brs t
substParsTag _         _          _   _ =
    error "Uniquify.substParsTag: Binder mismatch"

uniquify' :: TermV -> UniqueM TermV
uniquify' t@(Var _) = return t
uniquify' t@(Type _) = return t
uniquify' (App t₁ t₂) = App <$> uniquify' t₁ <*> uniquify' t₂
uniquify' (Arr b ty₁ ty₂) =
    do b' <- freshBinder b
       Arr b' <$> uniquify' ty₁ <*> uniquify' (substTag b b' ty₂)
uniquify' (Lam b ty t) =
    do b' <- freshBinder b
       Lam b' <$> uniquify' ty <*> uniquify' (substTag b b' t)
uniquify' (Case b t ty brs) =
    do b' <- freshBinder b
       Case b' <$> uniquify' t <*> uniquify' (substTag b b' ty)
               <*> uniquifyBrs (substBrsTag b b' brs)
uniquify' (Fix b pars ty t) =
    do b' <- freshBinder b
       (pars', ty') <- uncurry uniquifyPars (substParsTag b b' pars ty)
       Fix b pars' ty' <$> uniquify' (substTag b b' t)
uniquify' (Constr c tys ts) = Constr c <$> mapM uniquify' tys <*> mapM uniquify' ts

uniquifyBrs :: [BranchV] -> UniqueM [BranchV]
uniquifyBrs = mapM go
  where
    go :: BranchV -> UniqueM BranchV
    go (c, bs, t) = do bs_tas <- mapM (\b -> (,) b <$> fresh) bs
                       let t' = foldr (\(b, ta) t -> undefined) t bs_tas
                       return (c, [fmap (const ta) b | (b, ta) <- bs_tas], t')

uniquifyPars :: [ParamV] -> TermV -> UniqueM ([ParamV], TermV)
uniquifyPars pars ty = paramsFun uniquify' pars ty

instance Uniquify DataT
