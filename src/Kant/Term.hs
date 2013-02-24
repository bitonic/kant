{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
module Kant.Term
    ( -- * Modules, data declarations, terms.
      Id
    , ConId
    , Level
    , TName
    , Binder
    , BinderT
    , BinderV
    , bind
    , wild
    , ModuleT(..)
    , Module
    , ModuleV
    , TeleFT(..)
    , ScopeT
    , ScopeFT(..)
    , FixT(..)
    , DeclT(..)
    , Decl
    , DeclV
    , DataBodyT
    , DataBody
    , DataT(..)
    , ConstrT(..)
    , Constr
    , Proxy(..)
    , TermT(..)
    , Term
    , TermV
    , BranchFT(..)
    , BranchT
    , Branch
      -- * Smart constructors
    , lams
    , pis
    , arr
    , pi_
    , app
    , case_
    , dataD
    , fix
      -- * Utilities
    , ParamT
    , Param
    , ParamV
    , unrollApp
    , unrollArr
    , unrollArr'
    , moduleNames
    -- * Substitutions
    , Bound(..)
    , MonadSubst(..)
    , freshBinder
    , subst
    , substB
    , substTele
    , substBranch
    , substManyB
    ) where

import           Control.Arrow (first, second)
import           Control.Monad (liftM, ap)
import           Data.Foldable (foldrM)

import           Control.Monad.Identity (Identity(..))

import           Data.Proxy
import           Numeric.Natural

import           Kant.Name

{-
t     Term
ty    Terms that are types
v     Name
n     Id inside Name and Id in general
b     Binder
con   Constr
c     constructor Id
l     Level
br    Branch
i     For numbers, e.g. the number of things in patterns
par   Parameter
d     Data
env   Env
it    Item
ctx   Map TName Item
dds   Map TName Data
dd    Data
-}

-- | Identifiers for things
type Id = String
type ConId = Id
type TName = Name Id

-- | Type levels
type Level  = Natural

-- | A Kant module.
newtype ModuleT n = Module {unModule :: [DeclT n]}
    deriving (Show, Functor)
type Module = ModuleT TName
type ModuleV = ModuleT Id

type BinderT = Maybe
type Binder = BinderT TName
type BinderV = BinderT Id

wild :: BinderT a
wild = Nothing

bind :: a -> BinderT a
bind = Just

-- | Value or datatype declaration.
data DeclT n
    = Val Id (TermT n)
    | Data ConId (TeleFT DataT n)
    | Postulate Id (TermT n)
    deriving (Show, Functor)
type Decl = DeclT TName
type DeclV = DeclT Id

type DataBodyT n = TeleFT DataT n
type DataBody = DataBodyT TName

data DataT n = DataT Level [ConstrT n]
    deriving (Show, Functor)

data ConstrT n = ConstrT ConId (TeleFT Proxy n)
    deriving (Show, Functor)
type Constr = ConstrT TName
type ConstrV = ConstrT Id

-- | Terms for our language.  This is what we typecheck and reduce.
data TermT n
    = Var n
      -- | The type of types
    | Type Level
      -- | Function application.  To the left we expect either a 'Lam' or a
      --   'Fix'.
    | App (TermT n) (TermT n)
      -- | Constructor for arrow types, of type @(A : Type n) -> (A -> Type m) ->
      --   Type (n ⊔ m)@.
    | Arr (TermT n) (ScopeT n)
      -- | Lambda abstraction.
    | Lam (TermT n) (ScopeT n)
      -- TODO is this good enough, or do I have to scope the scrutined acrosso
      -- the whole thing?
      -- | Pattern matching.
    | Case (TermT n) (ScopeT n) [(ConId, BranchT n)]
      -- | An instance of some inductive data type created by the user.
    | Constr ConId         -- Constructor
             [TermT n]     -- Type parameters
             [TermT n]     -- Data Parameters
    | Fix (TeleFT FixT n)
    deriving (Show, Functor)
type Term = TermT TName
type TermV = TermT Id

data ScopeFT f n = Scope (BinderT n) (f n)
    deriving (Show, Functor)
type ScopeT = ScopeFT TermT

data BranchFT f n = Branch [BinderT n] (f n)
    deriving (Show, Functor)
type BranchT = BranchFT TermT
type Branch = BranchFT TermT TName
type BranchV = BranchFT TermT Id

data TeleFT f n = Tele [ParamT n] (f n)
    deriving (Show, Functor)

data FixT n = FixT (TermT n) (ScopeT n)
    deriving (Show, Functor)

-- | Folds a list of parameters.
params :: (TermT t -> BinderT t -> TermT t -> TermT t)
       -> [ParamT t] -> TermT t -> TermT t
params f pars t = foldr (\(v, t₁) t₂ -> f t₁ v t₂) t pars

-- | Like 'lam', but abstracts over several parameters
lams :: [ParamT t] -> TermT t -> TermT t
lams = params (\ty b t -> Lam ty (Scope b t))

-- | @lam : lams = pi_ : pis@.
pis :: [ParamT t] -> TermT t -> TermT t
pis = params (\ty₁ b ty₂ -> Arr ty₁ (Scope b ty₂))

-- | Non-dependent function, @A -> B@
pi_ :: TermT t -> BinderT t -> TermT t -> TermT t
pi_ ty₁ b ty₂ = Arr ty₁ (Scope b ty₂)

arr :: TermT t -> TermT t -> TermT t
arr ty = pi_ ty wild

-- | @app a b c@ will return the term corresponding to @a b c@, i.e. @a@ applied
--   to @b@ applied to @c@.  Fails with empty lists.
app :: [TermT a] -> TermT a
app = foldl1 App

-- | Dual of 'App'.
unrollApp :: TermT t -> (TermT t, [TermT t])
unrollApp (App t₁ t₂) = second (++ [t₂]) (unrollApp t₁)
unrollApp t           = (t, [])

-- | Parameters for binders - we mostly use it when forming things and for
--   data/type constructors.
type ParamT n = (BinderT n, TermT n)
type Param = ParamT TName
type ParamV = ParamT Id

-- | Dual of 'Arr' (but with more general types).
unrollArr :: Maybe Natural -> TermT t -> ([ParamT t], TermT t)
unrollArr n        (Arr ty₁ (Scope b ty₂)) | n == Nothing || n > Just 0 =
    first ((b, ty₁) :) (unrollArr (fmap (\n' -> n' - 1) n)  ty₂)
unrollArr (Just 0) ty                      = ([], ty)
unrollArr _        ty                      = ([], ty)

unrollArr' :: TermT t -> ([ParamT t], TermT t)
unrollArr' = unrollArr Nothing

moduleNames :: ModuleT t -> [Id]
moduleNames = concatMap go . unModule
  where
    go (Val n _)                            = [n]
    go (Postulate n _)                      = [n]
    go (Data tyc ((Tele _ (DataT _ cons)))) = tyc : map (\(ConstrT c _) -> c) cons

------

fix :: [(BinderT v, TermT v)] -> TermT v -> BinderT v -> TermT v -> TermT v
fix pars ty n t = Fix (Tele pars (FixT ty (Scope n t)))

case_ :: TermT v -> BinderT v -> TermT v -> [(ConId, [BinderT v], TermT v)] -> TermT v
case_ t b ty brs = Case t (Scope b ty) [(c, Branch bs t') | (c, bs, t') <- brs]

dataD :: ConId -> [(BinderT v, TermT v)] -> Level
      -> [(ConId, [(BinderT v, TermT v)])]
      -> DeclT v
dataD c pars l cons =
    Data c (Tele pars (DataT l [ ConstrT c' (Tele pars' Proxy)
                               | (c', pars') <- cons ]))

------

type UpFun v₁ v₂ = v₁ -> TermT v₂

class Bound f where
    travb :: (Eq a, Eq b, Monad m)
          => UpFun a b
          -> (BinderT a -> UpFun a b -> m (BinderT b, UpFun a b))
          -> f a -> m (f b)

instance Bound f => Bound (ScopeFT f) where
    travb f g (Scope b x) = do (b', f') <- g b f; Scope b' `liftM` travb f' g x

instance Bound f => Bound (BranchFT f) where
    travb f g (Branch bs t) =
        do (bs', f') <- foldrM (\b (bs₁, f₁) ->
                                 do (b', f₁') <- g b f₁; return (b' : bs₁, f₁'))
                        ([], f) bs
           Branch bs' `liftM` travb f' g t

instance (Bound f) => Bound (TeleFT f) where
    travb fo g (Tele pars' t) = go pars' [] fo
      where
        go [] out f = Tele out `liftM` travb f g t
        go ((b, ty) : in_) out f = do ty' <- travb f g ty
                                      (b', f') <- g b f
                                      go in_ (out ++ [(b', ty')]) f'

instance Bound FixT where
    travb f g (FixT ty s) = FixT `liftM` travb f g ty `ap` travb f g s

instance Bound TermT where
    travb f _ (Var v) = return (f v)
    travb _ _ (Type l) = return (Type l)
    travb f g (App t₁ t₂) = App `liftM` travb f g t₁ `ap` travb f g t₂
    travb f g (Arr ty s) = Arr `liftM` travb f g ty `ap` travb f g s
    travb f g (Lam ty s) = Lam `liftM` travb f g ty `ap` travb f g s
    travb f g (Case t s brs) =
        Case `liftM` travb f g t `ap` travb f g s `ap`
        sequence [(c,) `liftM` travb f g br | (c, br) <- brs]
    travb f g (Constr c ts tys) =
        Constr c `liftM` mapM (travb f g) ts `ap` mapM (travb f g) tys
    travb f g (Fix ft) = Fix `liftM` travb f g ft

instance Bound ConstrT where
    travb f g (ConstrT c pars) = ConstrT c `liftM` travb f g pars

instance Bound DataT where
    travb f g (DataT l cons) = DataT l `liftM` mapM (travb f g) cons

instance Bound DeclT where
    travb f g (Val n t) = Val n `liftM` travb f g t
    travb f g (Data c pars) = Data c `liftM` travb f g pars
    travb f g (Postulate n ty) = Postulate n `liftM` travb f g ty

instance Bound Proxy where
    travb _ _ Proxy = return Proxy

instance Bound ModuleT where
    travb f g (Module decls) = Module `liftM` mapM (travb f g) decls

class Monad m => MonadSubst m where
    fresh :: Name a -> m (Name a)

freshBinder :: MonadSubst m => Maybe (Name a) -> m (Maybe (Name a))
freshBinder Nothing = return Nothing
freshBinder (Just v) = Just `liftM` fresh v

instance MonadSubst Identity where
    fresh = Identity

subst :: (Eq a, Bound f, MonadSubst m)
      => Name a -> TermT (Name a) -> f (Name a) -> m (f (Name a))
subst v₁ t = travb (\v₂ -> if v₁ == v₂ then t else Var v₂) refresh
  where
    refresh Nothing f = return (Nothing, f)
    refresh (Just v₂) f =
        do v₃ <- fresh v₂
           return (Just v₃, \v₄ -> if v₂ == v₄ then Var v₃ else f v₄)

substC :: (Eq a, Bound f) => Name a -> TermT (Name a) -> f (Name a) -> f (Name a)
substC v t = runIdentity . subst v t

substTele :: (Eq a, MonadSubst m, Bound t)
          => TeleFT t (Name a) -> [TermT (Name a)] -> m (t (Name a))
substTele (Tele [] t) [] = return t
substTele (Tele ((Nothing, _) : pars) t) (_ : ts) =
    substTele (Tele pars t) ts
substTele (Tele ((Just v, _) : pars) t) (t' : ts) =
    (`substTele` ts) =<< subst v t' (Tele pars t)
substTele _ _ = error "substTele: list does not match args num"

substBranch :: (Eq a, MonadSubst m, Bound t)
            => BranchFT t (Name a) -> [TermT (Name a)] -> m (t (Name a))
substBranch (Branch [] t) [] = return t
substBranch (Branch (Nothing : bs) t) (_ : ts) =
    substBranch (Branch bs t) ts
substBranch (Branch (Just v : bs) t) (t' : ts) =
    (`substBranch` ts) =<< subst v t' (Branch bs t)
substBranch _ _ = error "substBranch: list does not match args num"

substManyB :: (Eq v, MonadSubst m, Bound f)
           => [(BinderT (Name v), TermT (Name v))] -> f (Name v)
           -> m (f (Name v))
substManyB pars t = foldrM (uncurry substB) t pars

substB :: (Eq a, MonadSubst m, Bound f)
       => BinderT (Name a) -> TermT (Name a) -> f (Name a) -> m (f (Name a))
substB Nothing  _ t  = return t
substB (Just v) t t' = subst v t t'

instance (Eq v, Eq (f (Name v)), Bound f) => Eq (ScopeFT f (Name v)) where
    Scope Nothing   t₁ == Scope _         t₂ = t₁ == t₂
    Scope _         t₁ == Scope Nothing   t₂ = t₁ == t₂
    Scope (Just v₁) t₁ == Scope (Just v₂) t₂ = t₁ == substC v₂ (Var v₁) t₂

instance (Eq v, Eq (f (Name v)), Bound f) => Eq (BranchFT f (Name v)) where
    Branch [] t₁ == Branch [] t₂ = t₁ == t₂
    Branch (Nothing : bs₁) t₁ == Branch (_ : bs₂) t₂ =
        Branch bs₁ t₁ == Branch bs₂ t₂
    Branch (_ : bs₁) t₁ == Branch (Nothing : bs₂) t₂ =
        Branch bs₁ t₁ == Branch bs₂ t₂
    Branch (Just v₁ : bs₁) t₁ == Branch (Just v₂ : bs₂) t₂ =
        Branch bs₁ t₁ == substC v₂ (Var v₁) (Branch bs₂ t₂)
    _ == _ = False

instance (Eq v, Eq (f (Name v)), Bound f) => Eq (TeleFT f (Name v)) where
    Tele [] t₁ == Tele [] t₂ =
        t₁ == t₂
    Tele ((Nothing, ty₁) : pars₁) t₁ == Tele ((_, ty₂) : pars₂) t₂ =
        ty₁ == ty₂ && Tele pars₁ t₁ == Tele pars₂ t₂
    Tele ((_, ty₁) : pars₁) t₁ == Tele ((Nothing, ty₂) : pars₂) t₂ =
        ty₁ == ty₂ && Tele pars₁ t₁ == Tele pars₂ t₂
    Tele ((Just v₁, ty₁) : pars₁) t₁ == Tele ((Just v₂, ty₂) : pars₂) t₂ =
        ty₁ == ty₂ && Tele pars₁ t₁ == substC v₂ (Var v₁) (Tele pars₂ t₂)
    _ == _ = False

deriving instance Eq v => Eq (DeclT (Name v))
deriving instance Eq v => Eq (DataT (Name v))
deriving instance Eq v => Eq (ConstrT (Name v))
deriving instance Eq v => Eq (TermT (Name v))
deriving instance Eq v => Eq (FixT (Name v))

-- Id eq
deriving instance Eq DeclV
deriving instance Eq (DataT Id)
deriving instance Eq ConstrV
deriving instance Eq (f Id) => Eq (TeleFT f Id)
deriving instance Eq TermV
deriving instance Eq (FixT Id)
deriving instance Eq (ScopeT Id)
deriving instance Eq (f Id) => Eq (BranchFT f Id)
