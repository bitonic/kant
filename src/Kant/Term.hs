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
    , startTag
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
    , TNameT
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

-- | Type to tag names uniquely
type Tag = Natural

startTag :: Tag
startTag = 0

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
type Data = DataT Id Tag
type DataV = DataT Void Id

-- | A constructor declaration.
type ConstrT fr tag = (ConId, [ParamT fr tag])
type Constr = ConstrT Id Tag
type ConstrV = ConstrT Void Id

-- | A 'Name' with an 'Id' name.
type TNameT fr tag = Name fr Id tag
type TName = TNameT Id Tag

-- | Terms for our language.  This is what we typecheck and reduce.
data TermT fr tag
    = Var (TNameT fr tag)
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
jumpBind ta₁ (Bind ta₂) x _ | ta₁ == ta₂ = x
jumpBind _   _          _ x = x

jumpBindPars :: Eq tag
             => b -> (a -> b -> b)
             -> (Binder tag -> TermT fr tag -> a)
             -> ([ParamT fr tag] -> b)
             -> tag
             -> [ParamT fr tag]
             -> Either b b
jumpBindPars z _ _ _ _ [] = Right z
jumpBindPars z op f g ta ((b, ty) : pars) =
    case if Bind ta == b then Right (g pars) else jumpBindPars z op f g ta pars of
        Right xs -> Right (x `op` xs)
        Left xs  -> Left (x `op` xs)
  where x = f b ty

subst :: Eq tag => tag -> TermT fr tag -> TermT fr tag -> TermT fr tag
subst ta₁ t (Var (Bound _ ta₂)) | ta₁ == ta₂ = t
subst _ _ t@(Var _) = t
subst _ _ t@(Type _) = t
subst ta t₁ (App t₂ t₃) = App (subst ta t₁ t₂) (subst ta t₁ t₃)
subst ta t (Arr b ty₁ ty₂) = Arr b (subst ta t ty₁) (substBind ta t b ty₂)
subst ta t₁ (Lam b ty t₂) = Lam b (subst ta t₁ ty) (substBind ta t₁ b t₂)
subst ta t₁ (Case b t₂ ty brs) =
    Case b (subst ta t₁ t₂) ty' brs'
  where
    (ty', brs') = jumpBind ta b (ty, brs) ((subst ta t₁ ty), substBrs ta t₁ brs)
subst ta t (Constr c tys ts) = Constr c (map (subst ta t) tys) (map (subst ta t) ts)
subst ta t₁ (Fix b pars ty t₂) =
    case substPars ta t₁ pars of
        Left pars'  -> Fix b pars' ty t₂'
        Right pars' -> Fix b pars' (subst ta t₁ ty) t₂'
  where t₂' = substBind ta t₁ b t₂

substBind :: Eq tag => tag -> TermT fr tag -> Binder tag -> TermT fr tag
          -> TermT fr tag
substBind ta t₁ b t₂ = jumpBind ta b t₂ (subst ta t₁ t₂)

substPars :: Eq tag
          => tag -> TermT fr tag -> [ParamT fr tag]
          -> Either [ParamT fr tag] [ParamT fr tag]
substPars ta t = jumpBindPars [] (:) (\b ty -> (b, subst ta t ty)) id ta

substBrs :: Eq tag => tag -> TermT fr tag -> [BranchT fr tag] -> [BranchT fr tag]
substBrs ta t₁ brs = [ (c, bs, if Bind ta `elem` bs then t₂ else subst ta t₁ t₂)
                     | (c, bs, t₂) <- brs ]

bindId :: (Eq tag, MonadPlus m) => tag -> TermT fr tag -> m Id
bindId ta₁ (Var (Bound n ta₂)) | ta₁ == ta₂ = return n
bindId _  (Var _) = mzero
bindId _  (Type _) = mzero
bindId ta  (App t₁ t₂) = bindId ta t₁ `mplus` bindId ta t₂
bindId ta  (Arr b ty₁ ty₂) = bindId ta ty₁ `mplus` bindIdBind ta ty₂ b
bindId ta  (Lam b ty t) = bindId ta ty `mplus` bindIdBind ta t b
bindId ta  (Case b t₁ ty brs) =
    bindId ta t₁ `mplus` jumpBind ta b mzero (bindId ta ty `mplus` bindIdBrs ta brs)
bindId ta  (Constr _ tys ts) = msum (map (bindId ta) (tys ++ ts))
bindId ta  (Fix b pars ty t) =
    case bindIdPars ta pars of
        Left mid -> mid `mplus` rest
        Right mid -> mid `mplus` bindId ta ty `mplus` rest
  where rest = bindIdBind ta t b

bindIdBind :: (Eq tag, MonadPlus m) => tag -> TermT fr tag -> Binder tag -> m Id
bindIdBind ta t b = jumpBind ta b mzero (bindId ta t)

bindIdPars :: (Eq tag, MonadPlus m) => tag -> [ParamT fr tag]
           -> Either (m Id) (m Id)
bindIdPars ta = jumpBindPars mzero mplus (\_ ty -> bindId ta ty) (const mzero) ta

bindIdBrs :: (Eq tag, MonadPlus m) => tag -> [BranchT fr tag] -> m Id
bindIdBrs ta brs =
    msum [if Bind ta `elem` bs then mzero else bindId ta t₂ | (_, bs, t₂) <- brs]

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

bindEq :: (Eq tag, Eq fr) => Binder tag -> TermT fr tag -> Binder tag
       -> TermT fr tag -> Bool
bindEq b t b' t' = t == bindSubst b t b' t'

bindSubst :: (Eq tag, Eq fr) => Binder tag -> TermT fr tag -> Binder tag
          -> TermT fr tag -> TermT fr tag
bindSubst Wild      _ _          t  = t
bindSubst _         _ Wild       t  = t
bindSubst (Bind ta) t (Bind ta') t' =
    case bindId ta t of
        Nothing -> t'
        Just n  -> subst ta' (Var (Bound n ta)) t'

brEq :: (Eq tag, Eq fr)
     => Binder tag -> [BranchT fr tag]
     -> Binder tag -> [BranchT fr tag]
     -> Bool
brEq Wild brs _    brs' = brEq' brs brs'
brEq _    brs Wild brs' = brEq' brs brs'
brEq (Bind ta) brs (Bind ta') brs' =
    case bindIdBrs ta brs of
        Nothing -> brEq' brs brs'
        Just n  -> brEq' brs (substBrs ta' (Var (Bound n ta)) brs)

brEq' :: (Eq tag, Eq fr) => [BranchT fr tag] -> [BranchT fr tag] -> Bool
brEq' [] [] = True
brEq' ((c, bs, t) : brs) ((c', bs', t') : brs') =
    c == c' && brEq' brs brs' && length bs == length bs' &&
    t == foldr (\(b, b') t'' -> bindSubst b t b' t'') t' (zip bs bs')
brEq' _ _ = False
