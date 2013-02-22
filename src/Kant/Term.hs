{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.Term
    ( -- * Modules, data declarations, terms.
      Id
    , Void
    , ConId
    , Level
    , Tag
    , Name(..)
    , Binder(..)
    , TBinderT
    , TBinder
    , ModuleT(..)
    , Module
    , ModuleV
    , ParamT
    , Param
    , ParamV
    , DeclT(..)
    , Decl
    , DeclV
    , DataT(..)
    , Data
    , DataV
    , ConstrT
    , Constr
    , ConstrV
    , TName
    , TermT(..)
    , Term
    , TermV
    , BranchT
    , Branch
    , BranchV
      -- * Smart constructors
    , bound
    , free
    , lams
    , arrs
    , arr
    , app
      -- * Utilities
    , unrollApp
    , unrollArr
    , unrollArr'
    , moduleNames
    , paramsFun
    , paramsFun'
      -- * Substitutions
    , subst
    , substPars
    , substBrs
    , subst'
    ) where

import           Control.Arrow (first, second)
import           Control.Monad (liftM)

import           Data.Text (Text)

import           Data.Void
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

-- | Type levels
type Level  = Natural

-- | A Kant module.
newtype ModuleT fr tag = Module {unModule :: [DeclT fr tag]}
    deriving (Show, Eq)
type Module = ModuleT Id Tag
type ModuleV = ModuleT Void Id

type TBinderT = Binder Id
type TBinder = TBinderT Tag

-- | Parameters for binders - we mostly use it when forming things and for
--   data/type constructors.
type ParamT fr tag = (TBinderT tag, TermT fr tag)
type Param = ParamT Id Tag
type ParamV = ParamT Void Id

-- | Value or datatype declaration.
data DeclT fr tag
    = Val Id (TermT fr tag)
    | DataD (DataT fr tag)
    | Postulate Id (TermT fr tag)
    deriving (Show, Eq)
type Decl = DeclT Id Tag
type DeclV = DeclT Void Id

-- | Inductive data types declarations.
data DataT fr tag
    = Data ConId            -- Name
           [ParamT fr tag]  -- Parameters' types
           Level            -- Resulting level
           [ConstrT fr tag] -- Constructors
    deriving (Show, Eq)
type Data = DataT Id Tag
type DataV = DataT Void Id

-- | A constructor declaration.
type ConstrT fr tag = (ConId, [ParamT fr tag])
type Constr = ConstrT Id Tag
type ConstrV = ConstrT Void Id

-- | A 'Name' with an 'Id' name.
type TName  = Name Id Tag

-- | Terms for our language.  This is what we typecheck and reduce.
data TermT fr tag
    = Var (Name fr tag)
      -- | The type of types
    | Type Level
      -- | Function application.  To the left we expect either a 'Lam' or a
      --   'Fix'.
    | App (TermT fr tag) (TermT fr tag)
      -- | Constructor for arrow types, of type @(A : Type n) -> (A -> Type m) ->
      --   Type (n ⊔ m)@.
    | Arr (TBinderT tag) (TermT fr tag) (TermT fr tag)
      -- | Lambda abstraction.
    | Lam (TBinderT tag) (TermT fr tag) (TermT fr tag)
      -- | Pattern matching.
    | Case (TBinderT tag)       -- Name for the scrutined
           (TermT fr tag)       -- Scrutined
           (TermT fr tag)       -- Return type
           [BranchT  fr tag]
      -- | An instance of some inductive data type created by the user.
    | Constr ConId              -- Constructor
             [TermT fr tag]     -- Type parameters
             [TermT fr tag]     -- Data Parameters
    | Fix (TBinderT tag)
          [ParamT fr tag]       -- Arguments to the function.
          (TermT fr tag)        -- Return type
          (TermT fr tag)        -- Body
    deriving (Show, Functor)
type Term = TermT Id Tag
type TermV = TermT Void Id

type BranchT fr tag = (ConId, [TBinderT tag], TermT fr tag)
type Branch = BranchT Id Tag
type BranchV = BranchT Void Id

bound :: t -> TermT f t
bound = Var . Bound

free :: f -> TermT f t
free = Var . Free

-- | Folds a list of parameters.
params :: (TBinderT t -> TermT f t -> TermT f t -> TermT f t)
       -> [ParamT f t] -> TermT f t -> TermT f t
params f pars t = foldr (\(v, t₁) t₂ -> f v t₁ t₂) t pars

-- | Like 'lam', but abstracts over several parameters
lams :: [ParamT f t] -> TermT f t -> TermT f t
lams = params Lam

-- | @lam : lams = pi_ : pis@.
arrs :: [ParamT f t] -> TermT f t -> TermT f t
arrs = params Arr

-- | Non-dependent function, @A -> B@
arr :: TermT f t -> TermT f t -> TermT f t
arr ty₁ ty₂ = Arr Wild ty₁ ty₂

-- | @app a b c@ will return the term corresponding to @a b c@, i.e. @a@ applied
--   to @b@ applied to @c@.  Fails with empty lists.
app :: [TermT f a] -> TermT f a
app = foldl1 App

-- | Dual of 'App'.
unrollApp :: TermT f t -> (TermT f t, [TermT f t])
unrollApp (App t₁ t₂) = second (++ [t₂]) (unrollApp t₁)
unrollApp t           = (t, [])

-- | Dual of 'Arr' (but with more general types).
unrollArr :: Maybe Natural -> TermT f t -> ([ParamT f t], TermT f t)
unrollArr n        (Arr b ty₁ ty₂) | n == Nothing || n > Just 0 =
    first ((b, ty₁) :) (unrollArr (fmap (\n' -> n' - 1) n)  ty₂)
unrollArr (Just 0) ty              = ([], ty)
unrollArr _        ty              = ([], ty)

paramsFun :: Monad m => (TermT f t -> m (TermT f' t')) -> [ParamT f t] -> TermT f t
          -> m ([ParamT f' t'], TermT f' t')
paramsFun f pars ty =
    unrollArr (Just (fromIntegral (length pars))) `liftM` f (arrs pars ty)

paramsFun' :: (TermT f t -> TermT f' t') -> [ParamT f t] -> TermT f t
           -> ([ParamT f' t'], TermT f' t')
paramsFun' f pars ty = x where Just x = paramsFun (Just . f) pars ty

unrollArr' :: TermT f t -> ([ParamT f t], TermT f t)
unrollArr' = unrollArr Nothing

moduleNames :: ModuleT f t -> [Id]
moduleNames = concatMap go . unModule
  where
    go (Val n _)                   = [n]
    go (Postulate n _)             = [n]
    go (DataD (Data tyc _ _ cons)) = tyc : map fst cons

------

jumpBind :: Eq tag => tag -> TBinderT tag -> a -> a -> a
jumpBind ta₁ (Bind _ ta₂) x _ | ta₁ == ta₂ = x
jumpBind _   _            _ x = x

subst :: Eq tag => tag -> TermT fr tag -> TermT fr tag -> TermT fr tag
subst ta₁ f (Var (Bound ta₂)) | ta₁ == ta₂ = f
subst _ _ t@(Var _) = t
subst _ _ t@(Type _) = t
subst ta f (App t₁ t₂) = App (subst ta f t₁) (subst ta f t₂)
subst ta f (Arr b ty₁ ty₂) = Arr b (subst ta f ty₁) (substBind ta f b ty₂)
subst ta f (Lam b ty t) = Lam b (subst ta f ty) (substBind ta f b t)
subst ta f (Case b t ty brs) =
    Case b (subst ta f t) ty' brs'
  where
    (ty', brs') = jumpBind ta b (ty, brs) ((subst ta f ty), substBrs ta f brs)
subst ta f (Constr c tys ts) = Constr c (map (subst ta f) tys) (map (subst ta f) ts)
subst ta f (Fix b pars ty t) = Fix b pars' ty' (substBind ta f b t)
  where (pars', ty') = substPars ta f pars ty

subst' :: Eq t => TBinderT t -> TermT f t -> TermT f t -> TermT f t
subst' Wild        _  t = t
subst' (Bind _ ta) t₁ t₂ = subst ta t₁ t₂

substBind :: Eq tag => tag -> TermT fr tag -> TBinderT tag -> TermT fr tag
          -> TermT fr tag
substBind ta f b t = jumpBind ta b t (subst ta f t)

substPars :: Eq tag
          => tag -> TermT fr tag -> [ParamT fr tag] -> TermT fr tag
          -> ([ParamT fr tag], TermT fr tag)
substPars ta t pars ty = paramsFun' (subst ta t) pars ty

substBrs :: Eq tag => tag -> TermT fr tag -> [BranchT fr tag] -> [BranchT fr tag]
substBrs ta t brs = [ (c, bs, if ta `bindElem` bs then t' else subst ta t t')
                    | (c, bs, t') <- brs ]

instance (Eq fr, Eq tag) => Eq (TermT fr tag) where
    Var n           == Var n'              = n == n'
    Type l          == Type l'             = l == l'
    App t₁ t₂       == App t₁' t₂'         = t₁ == t₁' && t₂ == t₂'
    Arr b ty₁ ty₂   == Arr b' ty₁' ty₂'    = ty₁ == ty₁' && bindEq b ty₂ b' ty₂'
    Lam b ty t      == Lam b' ty' t'       = ty == ty' && bindEq b t b' t'
    Constr c tys ts == Constr c' tys' ts'  = c == c' && tys == tys' && ts == ts'
    Fix b pars ty t == Fix b' pars' ty' t' =
        bindEq b (arrs pars ty) b' (arrs pars' ty') && bindEq b t b' t'
    Case b t ty brs == Case b' t' ty' brs' =
        t == t' && bindEq b ty b' ty' && brEq b brs b' brs'
    _               == _                   = False

bindEq :: (Eq tag, Eq fr) => TBinderT tag -> TermT fr tag -> TBinderT tag
       -> TermT fr tag -> Bool
bindEq b t b' t' = t == bindSubst b b' t'

bindSubst :: (Eq t, Eq f) => TBinderT t -> TBinderT t -> TermT f t -> TermT f t
bindSubst Wild        _            t  = t
bindSubst _           Wild         t  = t
bindSubst (Bind _ ta) (Bind _ ta') t' = subst ta' (bound ta) t'

brEq :: (Eq tag, Eq fr)
     => TBinderT tag -> [BranchT fr tag]
     -> TBinderT tag -> [BranchT fr tag]
     -> Bool
brEq Wild        brs _            brs' = brEq' brs brs'
brEq _           brs Wild         brs' = brEq' brs brs'
brEq (Bind _ ta) brs (Bind _ ta') brs' = brEq' brs (substBrs ta' (bound ta) brs')

brEq' :: (Eq tag, Eq fr) => [BranchT fr tag] -> [BranchT fr tag] -> Bool
brEq' [] [] = True
brEq' ((c, bs, t) : brs) ((c', bs', t') : brs') =
    c == c' && brEq' brs brs' && length bs == length bs' &&
    t == foldr (\(b, b') t'' -> bindSubst b b' t'') t' (zip bs bs')
brEq' _ _ = False
