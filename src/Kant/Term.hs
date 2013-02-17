{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Kant.Term
    ( -- * Abstract syntax tree
      Id
    , ConId
    , Level
    , Module(..)
    , Decl(..)
    , Data(..)
    , Val(..)
    , Constr
    , Param
    , TermT(..)
    , Term
    , BranchT
    , Branch
    , TName
    , TScopeT
    , TScopeT²
    , TScope
    , discarded
      -- * Smart constructors
    , lam
    , lams
    , pi_
    , pis
    , fix
    , arr
    , case_
    , app
    , params
      -- * Utilities
    , unrollApp
    , unrollArr
    , arrLen
    , instantiateList
    , scopeVars
    , scopeVar
    , moduleNames
    ) where

import           Control.Applicative (Applicative(..), (<$>))
import           Control.Arrow (first, second)
import           Control.Monad (ap)
import           Data.Foldable (Foldable)
import           Data.List (elemIndex)
import           Data.Maybe (listToMaybe)
import           Data.Traversable (Traversable)

import qualified Data.Set as Set

import           Bound
import           Bound.Name
import           Bound.Scope
import           Prelude.Extras

import           Kant.Common

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

newtype Module = Module {unModule :: [Decl]}
    deriving (Show, Eq)

-- TODO we can remove the type in ValD, since Fix include the recursive type
-- | Value or datatype declaration
data Decl
    = ValD Val
    | DataD Data
    | Postulate
          Id                    -- Name
          Term                  -- Type
    deriving (Show, Eq)

data Val = Val Id               -- Name
               Term             -- Type
               Term             -- Body
    deriving (Show, Eq)

-- | Inductive data types declarations.
--
--   The parameters stuff is basically an arrow type and in fact we could simply
--   use a 'Term', but I want to enforce more easily the fact that the return
--   type is either always a 'Type'n with type constructors or whatever the
--   datatype we are defining is with data constructors.  'dataDecl' can be used
--   to recover the types.
--
--   Note that each parameter is scoped through the rest of the list.  This
--   means that parameters in data constructors can shadow global parameters in
--   the type constructor.
data Data = Data ConId            -- Name
                 [Param]          -- Parameters' types
                 Level            -- Resulting level
                 [Constr]         -- Constructors
    deriving (Show, Eq)

type Constr = (ConId, [Param])
type Param = (Id, Term)

type TName a        = Name Id a
type TScopeT b a    = Scope (TName b) TermT a
type TScopeT² b c a = Scope (TName b) (Scope (TName c) TermT) a
type TScope a       = TScopeT () a

data TermT a
    = Var a
    | Type Level
    | App (TermT a) (TermT a)
      -- | The constructor for arrow types, of type @(A : Type n) -> (A -> Type m) ->
      --   Type (n ⊔ m)@.
    | Arr (TermT a) (TScope a)
    | Lam (TermT a) (TScope a)
    | Case (TermT a) (TScope a) [BranchT a]
    | Constr ConId [TermT a] [TermT a]
    | Fix (TermT a)                   -- The type of the rec function.
          (TScopeT² Int () a)         -- The body, scoped with the arguments
                                      -- (there should be as many as the length
                                      -- of the list) and the recursive
                                      -- function.
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

type Term = TermT Id

-- | Each branch is scoped with the matched variable, and the arguments to the
--   constructors.
type BranchT a = (ConId, Int, TScopeT² Int () a)
type Branch = BranchT Id

instance Eq1 TermT   where (==#)      = (==)
instance Ord1 TermT  where compare1   = compare
instance Show1 TermT where showsPrec1 = showsPrec
instance Read1 TermT where readsPrec1 = readsPrec
instance Applicative TermT where pure = Var; (<*>) = ap

instance Monad TermT where
    return = Var

    Var v            >>= f = f v
    Type l           >>= _ = Type l
    App t₁ t₂        >>= f = App (t₁ >>= f) (t₂ >>= f)
    Arr ty s         >>= f = Arr (ty >>= f) (s >>>= f)
    Lam t s          >>= f = Lam (t >>= f) (s >>>= f)
    Case t tys brs   >>= f = Case (t >>= f) (tys >>>= f)
                                  [(c, i, s >>>>= f) | (c, i, s) <- brs]
    Constr c tys ts  >>= f = Constr c (map (>>= f) tys) (map (>>= f) ts)
    Fix ty s         >>= f = Fix (ty >>= f) (s >>>>= f)

(>>>>=) :: TScopeT² b c a -> (a -> TermT d) -> TScopeT² b c d
Scope s >>>>= f = Scope (fmap (>>>= f) <$> s)

-- | A binding/pattern match that we are not going to use.
discarded :: Id
discarded = "_"

-- | Good 'ol lambda abstraction.
lam :: Id -> Term -> Term -> Term
lam v ty t = Lam ty (abstract1Name v t)

params :: (Id -> Term -> Term -> Term) -> [Param] -> Term -> Term
params f pars t = foldr (\(v, t₁) t₂ -> f v t₁ t₂) t pars

-- | Like 'lam', but abstracts over several parameters
lams :: [Param] -> Term -> Term
lams = params lam

-- | Pattern matching.
case_ :: Term                   -- ^ The scrutined
      -> Id                     -- ^ The abstracted var
      -> Term                   -- ^ The return type
      -> [(ConId, [Id], Term)]  -- ^ Each branch has a constructor, bound
                                --   variables, and a body.
      -> Term
case_ t n ty brs =
    Case t (abstract1Name n ty)
         [ (c, length vs, (abstractName (`elemIndex` vs) (abstract1Name n t')))
         | (c, vs, t') <- brs ]

-- | Dependent function, @(x : A) -> B@.
pi_ :: Id                       -- ^ Abstracting an @x@...
    -> Term                     -- ^ ...of type @A@..
    -> Term                     -- ^ ...over type @B@
    -> Term
pi_ v ty₁ ty₂ = Arr ty₁ (abstract1Name v ty₂)

-- | @lam : lams = pi_ : pis@.
pis :: [Param] -> Term -> Term
pis = params pi_

fix :: Id                       -- ^ Name of the recursor
    -> [Param]                  -- ^ Arguments
    -> Term                     -- ^ Return type
    -> Term                     -- ^ Body
    -> Term
fix n pars ty t = Fix (pis pars ty)
                  (abstractName (`elemIndex` map fst pars) (abstract1Name n t))

-- | Non-dependent function, @A -> B@
arr :: Term -> Term -> Term
arr ty₁ ty₂ = Arr ty₁ (toScope (F <$> ty₂))

-- | @app a b c@ will return the term corresponding to @a b c@, i.e. @a@ applied
--   to @b@ applied to @c@.  Fails with empty lists.
app :: [TermT a] -> TermT a
app = foldl1 App

unrollApp :: TermT a -> (TermT a, [TermT a])
unrollApp (App t₁ t₂) = second (++ [t₂]) (unrollApp t₁)
unrollApp t           = (t, [])

unrollArr :: Term -> ([Param], Term)
unrollArr (Arr ty s) = first ((n, ty) :) (unrollArr (instantiate1 (Var n) s))
  where n = case scopeVars s of
                []     -> discarded
                (n':_) -> n'
unrollArr t = ([], t)

arrLen :: TermT a -> Int
arrLen (Arr _ s) = 1 + arrLen (fromScope s)
arrLen _         = 0

scopeVars :: (Monad f, Foldable f, Ord n) => Scope (Name n b) f a -> [n]
scopeVars s = Set.toList (Set.fromList (map name (bindings s)))

scopeVar :: (Monad f, Foldable f, Ord n) => Scope (Name n ()) f a -> Maybe n
scopeVar = listToMaybe . scopeVars

-- | Instantiates an 'Int'-indexed scope where each number 'n' is replaced by
--   the element at index 'n' in the provided list.
--
--   IMPORTANT: this function is unsafe, it crashes if the list doesn't cover
--   all the indices in the term.
instantiateList :: Monad f => [f a] -> Scope (Name n Int) f a -> f a
instantiateList ts = instantiateName (ts !!)

moduleNames :: Module -> [Id]
moduleNames = concatMap go . unModule
  where
    go (ValD (Val n _ _))          = [n]
    go (Postulate n _)             = [n]
    go (DataD (Data tyc _ _ cons)) = tyc : map fst cons
