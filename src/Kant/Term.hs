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
    , substPars
    , substBrs
      -- * Bind names
    , bindId
    ) where

import           Control.Arrow (first, second)
import           Control.Monad (MonadPlus(..), msum)

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
    | Case (Binder tag)         -- Name for the scrutined
           (TermT fr tag)       -- Scrutined
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

jumpBind :: Eq tag => tag -> Binder tag -> a -> a -> a
jumpBind v₁ (Bind v₂) x _ | v₁ == v₂ = x
jumpBind _  _ _ x         = x

jumpBindPars :: Eq tag
             => b -> (a -> b -> b)
             -> (Binder tag -> TermT fr tag -> a)
             -> ([ParamT fr tag] -> b)
             -> tag
             -> [ParamT fr tag]
             -> Either b b
jumpBindPars z _ _ _ _ [] = Right z
jumpBindPars z op f g v ((b, ty) : pars) =
    case if Bind v == b then Right (g pars) else jumpBindPars z op f g v pars of
        Right pars' -> Right (bty `op` pars')
        Left pars'  -> Left (bty `op` pars')
  where bty = f b ty

subst :: Eq tag => tag -> TermT fr tag -> TermT fr tag -> TermT fr tag
subst v₁ t (Var (Bound _ v₂)) | v₁ == v₂ = t
subst _ _ t@(Var _) = t
subst _ _ t@(Type _) = t
subst v t₁ (App t₂ t₃) = App (subst v t₁ t₂) (subst v t₁ t₃)
subst v t (Arr b ty₁ ty₂) = Arr b (subst v t ty₁) (substBind v t b ty₂)
subst v t₁ (Lam b ty t₂) = Lam b (subst v t₁ ty) (substBind v t₁ b t₂)
subst v t₁ (Case b t₂ ty brs) =
    Case b (subst v t₁ t₂) ty' brs'
  where
    (ty', brs') = jumpBind v b (ty, brs) ((subst v t₁ ty), substBrs v t₁ brs)
subst v t (Constr c tys ts) = Constr c (map (subst v t) tys) (map (subst v t) ts)
subst v t₁ (Fix b pars ty t₂) =
    case substPars v t₁ pars of
        Left pars'  -> Fix b pars' ty t₂'
        Right pars' -> Fix b pars' (subst v t₁ ty) t₂'
  where t₂' = substBind v t₁ b t₂

substBind :: Eq tag => tag -> TermT fr tag -> Binder tag -> TermT fr tag
          -> TermT fr tag
substBind v t₁ b t₂ = jumpBind v b t₂ (subst v t₁ t₂)

substPars :: Eq tag
          => tag -> TermT fr tag -> [ParamT fr tag]
          -> Either [ParamT fr tag] [ParamT fr tag]
substPars v t = jumpBindPars [] (:) (\b ty -> (b, subst v t ty)) id v

substBrs :: Eq tag => tag -> TermT fr tag -> [BranchT fr tag] -> [BranchT fr tag]
substBrs v t₁ brs = [ (c, bs, if Bind v `elem` bs then t₂ else subst v t₁ t₂)
                    | (c, bs, t₂) <- brs ]

bindId :: (Eq tag, MonadPlus m) => tag -> TermT fr tag -> m Id
bindId v₁ (Var (Bound n v₂)) | v₁ == v₂ = return n
bindId _  (Var _) = mzero
bindId _  (Type _) = mzero
bindId v  (App t₁ t₂) = bindId v t₁ `mplus` bindId v t₂
bindId v  (Arr b ty₁ ty₂) = bindId v ty₁ `mplus` bindIdBind v ty₂ b
bindId v  (Lam b ty t) = bindId v ty `mplus` bindIdBind v t b
bindId v  (Case b t₁ ty brs) =
    bindId v t₁ `mplus` jumpBind v b mzero (bindId v ty `mplus` bindIdBrs v brs)
bindId v  (Constr _ tys ts) = msum (map (bindId v) (tys ++ ts))
bindId v  (Fix b pars ty t) =
    case bindIdPars v pars of
        Left mid -> mid `mplus` rest
        Right mid -> mid `mplus` bindId v ty `mplus` rest
  where rest = bindIdBind v t b

bindIdBind :: (Eq tag, MonadPlus m) => tag -> TermT fr tag -> Binder tag -> m Id
bindIdBind v t b = jumpBind v b mzero (bindId v t)

bindIdPars :: (Eq tag, MonadPlus m) => tag -> [ParamT fr tag]
           -> Either (m Id) (m Id)
bindIdPars v = jumpBindPars mzero mplus (\_ ty -> bindId v ty) (const mzero) v

bindIdBrs :: (Eq tag, MonadPlus m) => tag -> [BranchT fr tag] -> m Id
bindIdBrs v brs =
    msum [if Bind v `elem` bs then mzero else bindId v t₂ | (_, bs, t₂) <- brs]

instance (Eq fr, Eq tag) => Eq (TermT fr tag) where
    Var v           == Var v'              = v == v'
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

bindEq :: (Eq tag, Eq fr) => Binder tag -> TermT fr tag -> Binder tag
       -> TermT fr tag -> Bool
bindEq b t b' t' = t == bindSubst b t b' t'

bindSubst :: (Eq tag, Eq fr) => Binder tag -> TermT fr tag -> Binder tag
          -> TermT fr tag -> TermT fr tag
bindSubst Wild     _ _         t  = t
bindSubst _        _ Wild      t  = t
bindSubst (Bind v) t (Bind v') t' =
    case bindId v t of
        Nothing -> t'
        Just n  -> subst v' (Var (Bound n v)) t'

brEq :: (Eq tag, Eq fr)
     => Binder tag -> [BranchT fr tag]
     -> Binder tag -> [BranchT fr tag]
     -> Bool
brEq Wild brs _    brs' = brEq' brs brs'
brEq _    brs Wild brs' = brEq' brs brs'
brEq (Bind v) brs (Bind v') brs' =
    case bindIdBrs v brs of
        Nothing -> brEq' brs brs'
        Just n  -> brEq' brs (substBrs v' (Var (Bound n v)) brs)

brEq' :: (Eq tag, Eq fr) => [BranchT fr tag] -> [BranchT fr tag] -> Bool
brEq' [] [] = True
brEq' ((c, bs, t) : brs) ((c', bs', t') : brs') =
    c == c' && brEq' brs brs' && length bs == length bs' &&
    t == foldr (\(b, b') t'' -> bindSubst b t b' t'') t' (zip bs bs')
brEq' _ _ = False
