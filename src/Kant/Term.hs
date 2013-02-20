{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.Term
    ( -- * Modules, data declarations, terms.
      Id
    , Void
    , ConId
    , Level
    , Name(..)
    , Binder(..)
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
    , lams
    , arrs
    , arr
    , app
      -- * Utilities
    , unrollApp
    , unrollArr
    , moduleNames
      -- * Substitutions
    , subst
    ) where

import           Control.Arrow (first, second)

import           Data.Void
import           Numeric.Natural

import           Kant.Binder
import           Kant.Name

{-
t     Term
ty    Terms that are types
v     Name
n     Id inside Name and Id in general
con   Constr
c     constructor Id
l     Level
s     Scope
br    Branch
i     For numbers, e.g. the number of things in patterns
par   Parameter
d     Data
env   Env
-}

-- | Type to tag names uniquely
type Tag = Int

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

-- | Parameters for binders - we mostly use it when forming things and for
--   data/type constructors.
type ParamT fr tag = (Binder tag, TermT fr tag)
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
type Data = DataT Tag
type DataV = DataT Void

-- | A constructor declaration.
type ConstrT fr tag = (ConId, [ParamT fr tag])
type Constr = ConstrT Id Tag
type ConstrV = ConstrT Void Id

-- | A 'Name' with an 'Id' name.
type TName fr tag = Name fr Id tag

-- | Terms for our language.  This is what we typecheck and reduce.
data TermT fr tag
    = Var (TName fr tag)
      -- | The type of types
    | Type Level
      -- | Function application.  To the left we expect either a 'Lam' or a
      --   'Fix'.
    | App (TermT fr tag) (TermT fr tag)
      -- | Constructor for arrow types, of type @(A : Type n) -> (A -> Type m) ->
      --   Type (n ⊔ m)@.
    | Arr (Binder tag) (TermT fr tag) (TermT fr tag)
      -- | Lambda abstraction.
    | Lam (Binder tag) (TermT fr tag) (TermT fr tag)
      -- | Pattern matching.
    | Case (TName fr tag)       -- Variable to pattern match
           (TermT fr tag)       -- Return type
           [BranchT  fr tag]
      -- | An instance of some inductive data type created by the user.
    | Constr ConId              -- Constructor
             [TermT fr tag]     -- Type parameters
             [TermT fr tag]     -- Data Parameters
    | Fix (Binder tag)
          [ParamT fr tag]       -- Arguments to the function.
          (TermT fr tag)        -- Return type
          (TermT fr tag)        -- Body
    deriving (Show, Functor)
type Term = TermT Id Tag
type TermV = TermT Void Id

instance (Eq f, Eq t) => Eq (TermT f t) where

type BranchT fr tag = (ConId, [Binder tag], TermT fr tag)
type Branch = BranchT Id Tag
type BranchV = BranchT Void Id

-- | Folds a list of parameters.
params :: (Binder t -> TermT f t -> TermT f t -> TermT f t)
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
unrollArr :: TermT f t -> ([ParamT f t], TermT f t)
unrollArr (Arr b ty₁ ty₂) = first ((b, ty₁) :) (unrollArr ty₂)
unrollArr ty              = ([], ty)

moduleNames :: ModuleT f t -> [Id]
moduleNames = concatMap go . unModule
  where
    go (Val n _)                   = [n]
    go (Postulate n _)             = [n]
    go (DataD (Data tyc _ _ cons)) = tyc : map fst cons

------

substBind :: Eq tag => tag -> TermT fr tag -> Binder tag -> TermT fr tag
          -> TermT fr tag
substBind v₁ _  (Name v₂) t  | v₁ == v₂ = t
substBind v  t₁ _         t₂ = subst v t₁ t₂

subst :: Eq tag => tag -> TermT fr tag -> TermT fr tag -> TermT fr tag
subst v₁ t (Var (Bound _ v₂)) | v₁ == v₂ = t
subst _ _ t@(Var _) = t
subst _ _ t@(Type _) = t
subst v t₁ (App t₂ t₃) = App (subst v t₁ t₂) (subst v t₁ t₃)
subst v t (Arr b ty₁ ty₂) = Arr b (subst v t ty₁) (subst v t ty₂)
subst v t₁ (Lam b ty t₂) = Lam b (subst v t₁ ty) (substBind v t₁ b t₂)
subst v t₁ (Case n ty brs) =
    Case n (subst v t₁ ty)
         [ (c, bs, if Name v `elem` bs then t₂ else subst v t₁ t₂)
         | (c, bs, t₂) <- brs ]
subst v t (Constr c tys ts) = Constr c (map (subst v t) tys) (map (subst v t) ts)
subst v t₁ (Fix b pars ty t₂) =
    case substPars v t₁ pars of
        Left pars'  -> Fix b pars' ty t₂'
        Right pars' -> Fix b pars' (subst v t₁ ty) t₂'
  where t₂' = substBind v t₁ b t₂

substPars :: Eq tag
          => tag -> TermT fr tag -> [ParamT fr tag]
          -> Either [ParamT fr tag] [ParamT fr tag]
substPars _ _ [] = Right []
substPars v t ((b, ty) : pars) =
    case if Name v == b then Right pars else substPars v t pars of
        Right pars' -> Right (bty : pars')
        Left pars'  -> Left (bty : pars')
  where bty = (b, subst v t ty)
