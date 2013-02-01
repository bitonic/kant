{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Kant.Syntax
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
    , TScopeT
    , TScope
      -- * Commonly used things
    , arrow
    , discarded
      -- * Smart constructors
    , lam
    , lams
    , pi_
    , pis
    , arr
    , case_
    , app
    , valDecl
    , dataDecl
      -- * Utilities
    , uniquify
    , instantiateList
    ) where

import           Control.Applicative (Applicative(..))
import           Control.Monad (ap)
import           Data.Foldable (Foldable)
import           Data.List (elemIndex)
import           Data.Traversable (Traversable)

import           Bound
import           Bound.Name
import           Prelude.Extras

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

type Id = String
type ConId = Id
type Level  = Int
newtype Module = Module {unModule :: [Decl]}
    deriving (Show, Eq)

-- | Value or datatype declaration
data Decl
    = ValDecl Val
    | Postulate
          Id                    -- Name
          Term                  -- Type
    | DataDecl Data
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

type TScopeT a b = Scope (Name Id b) TermT a
type TScope a    = TScopeT a ()

data TermT a
    = Var a
    | Type Level
    | App (TermT a) (TermT a)
    | Lam (TermT a) (TScope a)
    | Case (TermT a) [BranchT a]
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

type Term = TermT Id

type BranchT a = (Id, Int, TScopeT a Int)
type Branch = BranchT Id

instance Eq1 TermT   where (==#)      = (==)
instance Ord1 TermT  where compare1   = compare
instance Show1 TermT where showsPrec1 = showsPrec
instance Read1 TermT where readsPrec1 = readsPrec
instance Applicative TermT where pure = Var; (<*>) = ap

instance Monad TermT where
    return = Var

    Var v      >>= f = f v
    Type l     >>= _ = Type l
    App t₁ t₂  >>= f = App (t₁ >>= f) (t₂ >>= f)
    Lam t s    >>= f = Lam (t >>= f) (s >>>= f)
    Case t brs >>= f = Case (t >>= f) (map (\(c, i, s) -> (c, i, s >>>= f)) brs)

-- | Good 'ol lambda abstraction.
lam :: Id -> Term -> Term -> Term
lam v ty t = Lam ty (abstract1Name v t)

params :: (Id -> Term -> Term -> Term) -> [Param] -> Term -> Term
params f pars t = foldr (\(v, t₁) t₂ -> f v t₁ t₂) t pars

-- | Like 'lam', but abstracts over several parameters
lams :: [Param] -> Term -> Term
lams = params lam

-- TODO This assumes that the variables are all distinct, fix that.
-- | Pattern matching
case_ :: Term
      -> [(ConId, [Id], Term)]  -- ^ Each branch has a constructor, bound
                                --   variables, and a body.
      -> Term
case_ t brs =
    Case t
         (map (\(c, vs, t') -> (c, length vs, (abstractName (`elemIndex` vs) t')))
              brs)

-- | A binding/pattern match that we are not going to use.
discarded :: Id
discarded = "_"

-- | The constructor for arrow types, of type @(A : Type) -> (A -> Type) ->
--   Type@.
arrow :: Term
arrow = Var "(->)"

-- | Dependent function, @(x : A) -> B@.
pi_ :: Id                       -- ^ Abstracting an @x@...
    -> Term                     -- ^ ...of type @A@..
    -> Term                     -- ^ ...over type @B@
    -> Term
pi_ v ty₁ ty₂ = app [arrow, ty₁, lam v ty₁ ty₂]

-- | @lam : lams = pi_ : pis@.
pis :: [Param] -> Term -> Term
pis = params pi_

-- | Non-dependent function, @A -> B@
arr :: Term -> Term -> Term
arr ty₁ ty₂ = app [arrow, ty₁, lam "_" ty₁ ty₂]

-- TODO should I keep this unsafe?
-- | @app a b c@ will return the term corresponding to @a b c@, i.e. @a@ applied
-- to @b@ applied to @c@.  Fails with empty lists.
app :: [Term] -> Term
app = foldr1 App

valDecl :: Id                   -- ^ Value name
        -> [Param]              -- ^ Function arguments
        -> Term                 -- ^ Return type
        -> Term                 -- ^ Body
        -> Val
valDecl n pars ty t = Val n (pis pars ty) (lams pars t)

-- | Extracts the types out of a data declaration.
--
--   A type function will be generated as type constructor, taking the
--   parameters as arguments and returning someting of @Type l@, where @l@ is
--   the level specified in the declaration.
--
--   Another function will be generated for each data constructor, taking all
--   the parameters of the type constructor plus its own parameter.
dataDecl :: Data -> ((Id, Term), [(Id, Term)])
dataDecl (Data c pars l cons) =
    ((c, params pi_ pars (Type l)),
     map (\(c', pars') -> (c', params pi_ (pars ++ pars') resTy)) cons)
  where
    resTy = app (Var c : map (Var . fst) pars)

-- TODO: Define this
-- | Makes all the 'Name's unique
uniquify :: TermT a -> TermT a
uniquify = id

-- | Instantiates an 'Int'-indexed scope where each number 'n' is replaced by
--   the element at index 'n' in the provided list.
--
--   IMPORTANT: this function is unsafe, it crashes if the list doesn't cover
--   all the indices in the term.
instantiateList :: Monad f => [f a] -> Scope (Name n Int) f a -> f a
instantiateList ts = instantiateName (ts !!)
