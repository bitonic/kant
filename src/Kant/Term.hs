{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
module Kant.Term
    ( -- * Modules, data declarations, terms.
      Id
    , ConId
    , Level
    , Tag
    , toId
    , toTag
    , Binder(..)
    , TBinderT
    , TBinder
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
    , arrs
    , arr
    , app
    , lamv
    , lamsv
    , arrv
    , fixv
    , casev
    , dataD
      -- * Utilities
    , unrollApp
    , unrollArr
    , unrollArr'
    , moduleNames
    -- * Substitutions
    , Subst(..)
    , substV
    , substManyV
    , substB
    , substManyB
    ) where

import           Control.Arrow (first, second)
import           Control.Monad (liftM, ap)
import           Data.Foldable (foldrM)
import           Data.Maybe (fromMaybe, catMaybes)

import           Data.Text (Text)
import qualified Data.Text as Text
import           Control.Monad.Identity (runIdentity)

import           Data.Proxy
import           Numeric.Natural

import           Kant.Binder

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

-- | Type to tag names uniquely.  Note that I use 'Text' and not 'String' only
--   so that the types are different.
type Tag = Text

-- | Identifiers for things
type Id = String
type ConId = Id

toId :: Tag -> Id
toId = Text.unpack

toTag :: Id -> Tag
toTag = Text.pack

-- | Type levels
type Level  = Natural

-- | A Kant module.
newtype ModuleT n = Module {unModule :: [DeclT n]}
    deriving (Show, Eq, Functor)
type Module = ModuleT Tag
type ModuleV = ModuleT Id

type TBinderT = Binder Id
type TBinder = TBinderT Tag

-- | Value or datatype declaration.
data DeclT n
    = Val Id (TermT n)
    | Data ConId (TeleFT DataT n)
    | Postulate Id (TermT n)
    deriving (Show, Eq, Functor)
type Decl = DeclT Tag
type DeclV = DeclT Id

type DataBodyT n = TeleFT DataT n
type DataBody = DataBodyT Tag

data DataT n = DataT Level [ConstrT n]
    deriving (Show, Eq, Functor)

data ConstrT n = ConstrT ConId (TeleFT Proxy n)
    deriving (Show, Eq, Functor)
type Constr = ConstrT Tag

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
    deriving (Show, Functor, Eq)
type Term = TermT Tag
type TermV = TermT Id

data ScopeFT f n = Scope (TBinderT n) (f n)
    deriving (Show, Functor)
type ScopeT = ScopeFT TermT

data BranchFT f n = Branch [TBinderT n] (f n)
    deriving (Show, Functor)
type BranchT = BranchFT TermT
type Branch = BranchFT TermT Tag

data TeleFT f n = Tele [ParamT n] (f n)
    deriving (Show, Functor)

data FixT n = FixT (TermT n) (ScopeT n)
    deriving (Show, Functor, Eq)

-- | Folds a list of parameters.
params :: (TermT t -> TBinderT t -> TermT t -> TermT t)
       -> [ParamT t] -> TermT t -> TermT t
params f pars t = foldr (\(v, t₁) t₂ -> f t₁ v t₂) t pars

-- | Like 'lam', but abstracts over several parameters
lams :: [ParamT t] -> TermT t -> TermT t
lams = params (\ty b t -> Lam ty (Scope b t))

-- | @lam : lams = pi_ : pis@.
arrs :: [ParamT t] -> TermT t -> TermT t
arrs = params (\ty₁ b ty₂ -> Arr ty₁ (Scope b ty₂))

-- | Non-dependent function, @A -> B@
arr :: TermT t -> TermT t -> TermT t
arr ty₁ ty₂ = Arr ty₁ (Scope Wild ty₂)

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
type ParamT n = (TBinderT n, TermT n)

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

lamsv :: [(Maybe Id, TermV)] -> TermV -> TermV
lamsv pars = lams (map (first toBinder) pars)

arrv :: TermV -> Maybe Id -> TermV -> TermV
arrv ty₁ n ty₂ = Arr ty₁ (Scope (toBinder n) ty₂)

lamv :: TermV -> Maybe Id -> TermV -> TermV
lamv ty n t = Lam ty(Scope (toBinder n) t)

paramsv :: [(Maybe Id, TermV)] -> f Id -> TeleFT f Id
paramsv pars t = Tele (map (first toBinder) pars) t

fixv :: [(Maybe Id, TermV)] -> TermV -> Maybe Id -> TermV -> TermV
fixv pars ty n t =
    Fix (paramsv pars (FixT ty (Scope (toBinder n) t)))

casev :: TermV -> Maybe Id -> TermV -> [(ConId, [Maybe Id], TermV)] -> TermV
casev t b ty brs = Case t (Scope (toBinder b) ty)
                        [(c, Branch (map toBinder bs) t') | (c, bs, t') <- brs]

dataD :: ConId -> [(Maybe Id, TermV)] -> Level
      -> [(ConId, [(Maybe Id, TermV)])]
      -> DeclV
dataD c pars l cons =
    Data c (paramsv pars (DataT l [ ConstrT c' (paramsv pars' Proxy)
                                  | (c', pars') <- cons ]))

------

type UpFun v = v -> TermT v

class Subst f where
    subst :: (Eq v, Monad m)
          => UpFun v
          -> (Binder Id v -> UpFun v -> m (Binder Id v, UpFun v))
          -> f v -> m (f v)

instance Subst f => Subst (ScopeFT f) where
    subst f g (Scope b x) = do (b', f') <- g b f; Scope b' `liftM` subst f' g x

instance Subst f => Subst (BranchFT f) where
    subst f g (Branch bs t) =
        do (bs', f') <- foldrM (\b (bs₁, f₁) ->
                                 do (b', f₁') <- g b f₁; return (b' : bs₁, f₁'))
                        ([], f) bs
           Branch bs' `liftM` subst f' g t

instance (Subst f) => Subst (TeleFT f) where
    subst fo g (Tele pars' t) = go pars' [] fo
      where
        go [] out f = Tele out `liftM` subst f g t
        go ((b, ty) : in_) out f = do ty' <- subst f g ty
                                      (b', f') <- g b f
                                      go in_ (out ++ [(b', ty')]) f'

instance Subst FixT where
    subst f g (FixT ty s) = FixT `liftM` subst f g ty `ap` subst f g s

instance Subst TermT where
    subst f _ (Var v) = return (f v)
    subst _ _ (Type l) = return (Type l)
    subst f g (App t₁ t₂) = App `liftM` subst f g t₁ `ap` subst f g t₂
    subst f g (Arr ty s) = Arr `liftM` subst f g ty `ap` subst f g s
    subst f g (Lam ty s) = Lam `liftM` subst f g ty `ap` subst f g s
    subst f g (Case t s brs) =
        Case `liftM` subst f g t `ap` subst f g s `ap`
        sequence [(c,) `liftM` subst f g br | (c, br) <- brs]
    subst f g (Constr c ts tys) =
        Constr c `liftM` mapM (subst f g) ts `ap` mapM (subst f g) tys
    subst f g (Fix ft) = Fix `liftM` subst f g ft

instance Subst ConstrT where
    subst f g (ConstrT c pars) = ConstrT c `liftM` subst f g pars

instance Subst DataT where
    subst f g (DataT l cons) = DataT l `liftM` mapM (subst f g) cons

instance Subst DeclT where
    subst f g (Val n t) = Val n `liftM` subst f g t
    subst f g (Data c pars) = Data c `liftM` subst f g pars
    subst f g (Postulate n ty) = Postulate n `liftM` subst f g ty

instance Subst Proxy where
    subst _ _ Proxy = return Proxy

instance Subst ModuleT where
    subst f g (Module decls) = Module `liftM` mapM (subst f g) decls

substV :: (Eq a, Subst f) => a -> TermT a -> f a -> f a
substV v₁ t = runIdentity .
              subst (\v₂ -> if v₁ == v₂ then t else Var v₂)
                    (\b f -> return (b, \v₃ -> case b of
                                                    Bind _ v₂ | v₂ == v₃ -> Var v₃
                                                    _ -> f v₃))

substManyV :: (Eq a, Subst f) => [(a, TermT a)] -> f a -> f a
substManyV pars =
    runIdentity .
    subst (\v -> fromMaybe (Var v) (lookup v pars))
          (\b f -> return (b, \v' -> case b of
                                         Bind _ v | v == v' -> Var v
                                         _ -> f v'))

substB :: (Eq v, Subst f) => Binder t v -> TermT v -> f v -> f v
substB Wild _ t = t
substB (Bind _ v) t t' = substV v t t'

substManyB :: Subst f => [(TBinder, Term)] -> f Tag -> f Tag
substManyB [] t = t
substManyB ((Wild, _) : pars) t = substManyB pars t
substManyB ((Bind _ v, t) : pars) t' = substManyB pars t''
  where Branch _ t'' = substV v t (Branch (map fst pars) t')

instance (Eq v, Eq (f v), Subst f) => Eq (ScopeFT f v) where
    Scope Wild        t₁ == Scope _           t₂ = t₁ == t₂
    Scope _           t₁ == Scope Wild        t₂ = t₁ == t₂
    Scope (Bind _ v₁) t₁ == Scope (Bind _ v₂) t₂ = t₁ == substV v₂ (Var v₁) t₂

instance (Eq v, Eq (f v), Subst f) => Eq (BranchFT f v) where
    Branch bs₁ t₁ == Branch bs₂ t₂ =
        t₁ == substManyV (catMaybes (zipWith merge bs₂ bs₁)) t₂
      where merge Wild        _           = Nothing
            merge _           Wild        = Nothing
            merge (Bind _ v₂) (Bind _ v₁) = Just (v₂, Var v₁)

instance (Eq v, Eq (f v), Subst f) => Eq (TeleFT f v) where
    Tele [] t₁ == Tele [] t₂ =
        t₁ == t₂
    Tele ((Wild, ty₁) : pars₁) t₁ == Tele ((_, ty₂) : pars₂) t₂ =
        ty₁ == ty₂ && Tele pars₁ t₁ == Tele pars₂ t₂
    Tele ((_, ty₁) : pars₁) t₁ == Tele ((Wild, ty₂) : pars₂) t₂ =
        ty₁ == ty₂ && Tele pars₁ t₁ == Tele pars₂ t₂
    Tele ((Bind _ v₁, ty₁) : pars₁) t₁ == Tele ((Bind _ v₂, ty₂) : pars₂) t₂ =
        ty₁ == ty₂ && Tele pars₁ t₁ == substV v₂ (Var v₁) (Tele pars₂ t₂)
    _ == _ = False
