{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Kant.Syntax
    ( Id
    , Level
    , Module(..)
    , Decl(..)
    , Data(..)
    , Constr
    , Params
    , TermT(..)
    , Term
    , TScopeT
    , TScope
    , lam
    , abs_
    , case_
    , app
    , dataDecl
    , uniquify
    ) where

import           Control.Applicative (Applicative(..))
import           Control.Monad (ap)
import           Data.Foldable (Foldable)
import           Data.List (elemIndex)
import           Data.Traversable (Traversable)

import           Bound
import           Bound.Name
import           Prelude.Extras

type Id = String
type Level  = Int
newtype Module = Module {unModule :: [Decl]}

data Decl
    = Val Id                      -- ^ Name
          Term                    -- ^ Body
    | DataDecl Data
    deriving (Show, Eq)

data Data = Data Id               -- ^ Name
                 Params           -- ^ Parameters' types
                 Level            -- ^ Resulting level
                 [Constr]         -- ^ Constructors
    deriving (Show, Eq)

type Constr = (Id, Params)

-- | Parameters for type and data constructors.  This is basically an arrow type
--   and in fact we could simply use a term, but I want to enforce more easily
--   the fact that the return type is either always a Typen with type
--   constructors or whatever the datatype we are defining is with data
--   constructors.
--
--   Note that each parameter is scoped through the rest of the list.  This
--   means that parameters in data constructors can shadow global parameters in
--   the type constructor.
type Params = [(Id, Term)]

type TVar v      = Name Id v
type TScopeT a v = Scope (TVar v) TermT a
type TScope a    = TScopeT a ()

data TermT a
    = Var a
    | Type Level
    | App (TermT a) (TermT a)
    | Lam (TermT a) (TScope a)
    | Case (TermT a) [(Id, Int, TScopeT a Int)]
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

type Term = TermT Id

instance Eq1 TermT   where (==#)      = (==)
instance Ord1 TermT  where compare1   = compare
instance Show1 TermT where showsPrec1 = showsPrec
instance Read1 TermT where readsPrec1 = readsPrec
instance Applicative TermT where pure = Var; (<*>) = ap

instance Monad TermT where
    return = Var

    Var v     >>= f = f v
    Type l    >>= _ = Type l
    App t m   >>= f = App (t >>= f) (m >>= f)
    Lam t s   >>= f = Lam (t >>= f) (s >>>= f)
    Case t bs >>= f = Case (t >>= f) (map (\(c,n,s) -> (c, n, s >>>= f)) bs)

lam :: Id -> Term -> Term -> Term
lam v ty t = Lam ty (abstract1Name v t)

-- TODO This assumes that the variables are all distinct, fix that.
case_ :: Term -> [(Id, [Id], Term)] -> Term
case_ t bs =
    Case t (map (\(c, vs, m) -> (c, length vs, (abstractName (`elemIndex` vs) m)))
                bs)

arrow :: Term
arrow = Var "(->)"

-- | Dependent function, @(x : A) -> B@
abs_ :: Id                       -- ^ Abstracting an @x@...
     -> Term                     -- ^ ...of type @A@..
     -> Term                     -- ^ ...over type @B@
     -> Term
abs_ v ty1 ty2 = app [arrow, ty1, lam v ty1 ty2]

app :: [Term] -> Term
app = foldr1 App

-- | Extracts the types out of a data declaration.
--
--   A type function will be generated as type constructor, taking the
--   parameters as arguments and returning someting of @Type l@, where @l@ is
--   the level specified in the declaration.
--
--   Another function will be generated for each data constructor, taking all
--   the parameters of the type constructor plus its own parameter.
dataDecl :: Data -> ((Id, Term), [(Id, Term)])
dataDecl (Data v pars l cons) =
    ((v, rev (Type l) pars),
     map (\(c, pars') -> (c, rev resTy (pars ++ pars'))) cons)
  where
    rev   = foldr (\(v', t) m -> abs_ v' t m)
    resTy = app (Var v : map (Var . fst) pars)

-- TODO: Define this
-- | Makes all the 'Name's unique
uniquify :: TermT a -> TermT a
uniquify = id
