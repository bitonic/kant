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
    , Name(..)
    , Binder(..)
    , TBinderT
    , TBinder
    , ModuleT(..)
    , Module
    , ModuleV
    , ParamT
    , ParamsFT(..)
    , Param
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
      -- * Smart constructors
    , lams
    , arrs
    , arr
    , app
    , lamv
    , arrv
    , fixv
    , casev
    , dataD
      -- * Utilities
    , unrollApp
    , unrollArr
    , unrollArr'
    , moduleNames
    , paramsFun
    , paramsFun'
    -- * Substitutions
    , Subst(..)
    , substV
    , substManyV
    -- , subst
    -- , substPars
    -- , substBrs
    -- , subst'
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
import           Kant.Name

{-
t     Term
ty    Terms that are types
v     Name
n     Id inside Name and Id in general
ta    the no-id part in the TName
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
    deriving (Show, Eq)
type Module = ModuleT Tag
type ModuleV = ModuleT Id

type TBinderT = Binder Id
type TBinder = TBinderT Tag

-- | Parameters for binders - we mostly use it when forming things and for
--   data/type constructors.
type ParamT n = (TBinderT n, TermT n)
type Param = ParamT Tag

-- | Value or datatype declaration.
data DeclT n
    = Val Id (TermT n)
    | Data ConId (ParamsFT DataT n)
    | Postulate Id (TermT n)
    deriving (Show, Eq, Functor)
type Decl = DeclT Tag
type DeclV = DeclT Id

type DataBodyT n = ParamsFT DataT n
type DataBody = DataBodyT Tag

data DataT n = DataT Level [ConstrT n]
    deriving (Show, Eq, Functor)

data ConstrT n = ConstrT ConId (ParamsFT Proxy n)
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
    | Fix (ParamsFT FixT n)
    deriving (Show, Functor, Eq)
type Term = TermT Tag
type TermV = TermT Id

data ScopeFT f n = Scope (TBinderT n) (f n)
    deriving (Show, Functor)
type ScopeT = ScopeFT TermT

data BranchFT f n = Branch [TBinderT n] (f n)
    deriving (Show, Functor)
type BranchT = BranchFT TermT

data ParamsFT f n = ParamsT [ParamT n] (f n)
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

-- | Dual of 'Arr' (but with more general types).
unrollArr :: Maybe Natural -> TermT t -> ([ParamT t], TermT t)
unrollArr n        (Arr ty₁ (Scope b ty₂)) | n == Nothing || n > Just 0 =
    first ((b, ty₁) :) (unrollArr (fmap (\n' -> n' - 1) n)  ty₂)
unrollArr (Just 0) ty                      = ([], ty)
unrollArr _        ty                      = ([], ty)

paramsFun :: Monad m => (TermT t -> m (TermT t')) -> [ParamT t] -> TermT t
          -> m ([ParamT t'], TermT t')
paramsFun f pars ty =
    unrollArr (Just (fromIntegral (length pars))) `liftM` f (arrs pars ty)

paramsFun' :: (TermT t -> TermT t') -> [ParamT t] -> TermT t
           -> ([ParamT t'], TermT t')
paramsFun' f pars ty = x where Just x = paramsFun (Just . f) pars ty

unrollArr' :: TermT t -> ([ParamT t], TermT t)
unrollArr' = unrollArr Nothing

moduleNames :: ModuleT t -> [Id]
moduleNames = concatMap go . unModule
  where
    go (Val n _)                               = [n]
    go (Postulate n _)                         = [n]
    go (Data tyc ((ParamsT _ (DataT _ cons)))) = tyc : map (\(ConstrT c _) -> c) cons

------

maybeToBind :: Maybe a -> Binder a a
maybeToBind Nothing = Wild
maybeToBind (Just x) = Bind x x

arrv :: TermV -> Maybe Id -> TermV -> TermV
arrv ty₁ n ty₂ = Arr ty₁ (Scope (maybeToBind n) ty₂)

lamv :: TermV -> Maybe Id -> TermV -> TermV
lamv ty n t = Lam ty(Scope (maybeToBind n) t)

paramsv :: [(Maybe Id, TermV)] -> f Id -> ParamsFT f Id
paramsv pars t = ParamsT (map (first maybeToBind) pars) t

fixv :: [(Maybe Id, TermV)] -> TermV -> Maybe Id -> TermV -> TermV
fixv pars ty n t =
    Fix (paramsv pars (FixT ty (Scope (maybeToBind n) t)))

casev :: TermV -> Maybe Id -> TermV -> [(ConId, [Maybe Id], TermV)] -> TermV
casev t b ty brs = Case t (Scope (maybeToBind b) ty)
                        [(c, Branch (map maybeToBind bs) t') | (c, bs, t') <- brs]

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

instance (Subst f) => Subst (ParamsFT f) where
    subst fo g (ParamsT pars' t) = go pars' [] fo
      where
        go [] out f = ParamsT out `liftM` subst f g t
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

instance (Eq v, Eq (f v), Subst f) => Eq (ParamsFT f v) where
    ParamsT [] t₁ == ParamsT [] t₂ =
        t₁ == t₂
    ParamsT ((Wild, ty₁) : pars₁) t₁ == ParamsT ((_, ty₂) : pars₂) t₂ =
        ty₁ == ty₂ && ParamsT pars₁ t₁ == ParamsT pars₂ t₂
    ParamsT ((_, ty₁) : pars₁) t₁ == ParamsT ((Wild, ty₂) : pars₂) t₂ =
        ty₁ == ty₂ && ParamsT pars₁ t₁ == ParamsT pars₂ t₂
    ParamsT ((Bind _ v₁, ty₁) : pars₁) t₁ == ParamsT ((Bind _ v₂, ty₂) : pars₂) t₂ =
        ty₁ == ty₂ && ParamsT pars₁ t₁ == substV v₂ (Var v₁) (ParamsT pars₂ t₂)
    _ == _ = False
