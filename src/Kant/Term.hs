{-# LANGUAGE DeriveFunctor #-}
module Kant.Term
    ( -- * Modules, data declarations, terms.
      Id
    , ConId
    , Level
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

-- | Binder
type TBinder = Binder Id

-- | A Kant module.
newtype ModuleT tag = Module {unModule :: [DeclT tag]}
    deriving (Show, Eq)
type Module = ModuleT Tag
type ModuleV = ModuleT Void

-- | Parameters for binders - we mostly use it when forming things and for
--   data/type constructors.
type ParamT tag = (TBinder, TermT tag)
type Param = ParamT Tag
type ParamV = ParamT Void

-- | Value or datatype declaration.
data DeclT tag
    = Val Id (TermT tag)
    | DataD (DataT tag)
    | Postulate Id (TermT tag)
    deriving (Show, Eq)
type Decl = DeclT Tag
type DeclV = DeclT Void

-- | Inductive data types declarations.
data DataT tag = Data ConId            -- Name
                      [ParamT tag]     -- Parameters' types
                      Level            -- Resulting level
                      [ConstrT tag]    -- Constructors
    deriving (Show, Eq)
type Data = DataT Tag
type DataV = DataT Void

-- | A constructor declaration.
type ConstrT tag = (ConId, [ParamT tag])
type Constr = ConstrT Tag
type ConstrV = ConstrT Void

-- | A 'Name' with an 'Id' name.
type TName tag = Name Id Id tag

-- | Terms for our language.  This is what we typecheck and reduce.
data TermT tag
    = Var (TName tag)
      -- | The type of types
    | Type Level
      -- | Function application.  To the left we expect either a 'Lam' or a
      --   'Fix'.
    | App (TermT tag) (TermT tag)
      -- | Constructor for arrow types, of type @(A : Type n) -> (A -> Type m) ->
      --   Type (n ⊔ m)@.
    | Arr TBinder (TermT tag) (TermT tag)
      -- | Lambda abstraction.
    | Lam TBinder (TermT tag) (TermT tag)
      -- | Pattern matching.
    | Case (TName tag)          -- Variable to pattern match
           (TermT tag)          -- Return type
           [BranchT tag]
      -- | An instance of some inductive data type created by the user.
    | Constr ConId              -- Constructor
             [TermT tag]        -- Type parameters
             [TermT tag]        -- Data Parameters
    | Fix TBinder
          (TermT tag)           -- Type of the rec function.
          [ParamT tag]          -- Arguments to the function.
          (TermT tag)           -- Body
    deriving (Eq, Show, Functor)
type Term = TermT Tag
type TermV = TermT Void

type BranchT tag = (ConId, [TBinder], TermT tag)
type Branch = BranchT Tag
type BranchV = BranchT Void

-- | Folds a list of parameters.
params :: (TBinder -> TermT t -> TermT t -> TermT t)
       -> [ParamT t] -> TermT t -> TermT t
params f pars t = foldr (\(v, t₁) t₂ -> f v t₁ t₂) t pars

-- | Like 'lam', but abstracts over several parameters
lams :: [ParamT t] -> TermT t -> TermT t
lams = params Lam

-- | @lam : lams = pi_ : pis@.
arrs :: [ParamT t] -> TermT t -> TermT t
arrs = params Arr

-- | Non-dependent function, @A -> B@
arr :: TermT t -> TermT t -> TermT t
arr ty₁ ty₂ = Arr Wild ty₁ ty₂

-- | @app a b c@ will return the term corresponding to @a b c@, i.e. @a@ applied
--   to @b@ applied to @c@.  Fails with empty lists.
app :: [TermT a] -> TermT a
app = foldl1 App

-- | Dual of 'App'.
unrollApp :: TermT t -> (TermT t, [TermT t])
unrollApp (App t₁ t₂) = second (++ [t₂]) (unrollApp t₁)
unrollApp t           = (t, [])

-- | Dual of 'Arr' (but with more general types).
unrollArr :: TermT t -> ([ParamT t], TermT t)
unrollArr (Arr b ty₁ ty₂) = first ((b, ty₁) :) (unrollArr ty₂)
unrollArr ty              = ([], ty)

moduleNames :: ModuleT t -> [Id]
moduleNames = concatMap go . unModule
  where
    go (Val n _)                   = [n]
    go (Postulate n _)             = [n]
    go (DataD (Data tyc _ _ cons)) = tyc : map fst cons
