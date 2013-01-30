{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Kant.Syntax where
    -- ( IdT
    -- , IdName
    -- , rawId
    -- , ConId
    -- , Level
    -- , Module
    -- , DeclT(..)
    -- , Decl
    -- , BranchT(..)
    -- , Branch
    -- , TermT(..)
    -- , Term
    -- , subst
    -- , unRaw
    -- , freshen
    -- ) where

import           Control.Applicative (Applicative(..), (<$>), (<*>))
import           Control.Arrow (second)
import           Control.Monad (ap)
import           Data.Foldable (Foldable)
import           Data.Maybe (fromMaybe)
import           Data.Traversable (Traversable)
import           Data.List (elemIndex)

import           Control.Monad.State (State, get, put, evalState)

import           Data.Map (Map)
import qualified Data.Map as Map

import           Bound
import           Bound.Name
import           Prelude.Extras

type Id = String
type ConId  = String
type Level  = Int
type Module = [Decl]

data Decl
    = Val Id                      -- ^ Name
          Term                    -- ^ Type
          [Branch]                -- ^ Branches
    | Data
          Id                      -- ^ Name
          Params                  -- ^ Parameters' types
          Level                   -- ^ Resulting level
          [Constr]                -- ^ Constructors
    deriving (Show, Eq)

type Constr = (ConId, Params)

-- | Parameters for type and data constructors.  This is basically an arrow type
--   and in fact we could simply use a term, but I want to enforce more easily
--   the fact that the return type is either always a Typen with type
--   constructors or whatever the datatype we are defining is with data
--   constructors.
--
--   Note that each parameter is scoped through the rest of the list.  This
--   means that parameters in data constructors can shadow global parameters in
--   the type constructor.
newtype Params = Params {unParams :: [(Id, Term)]}
    deriving (Show, Eq)

type TVar v      = Name Id v
type TScopeT a v = Scope (TVar v) TermT a
type TScope a    = TScopeT a ()

data Branch  = Branch ConId              -- ^ Matching a constructor
                      (TScopeT Id Int)   -- ^ Variables abstracted by index
    deriving (Show, Eq)

data TermT a
    = Var a
    | Type Level
    | App (TermT a) (TermT a)
    | Lam (TermT a) (TScope a)
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

type Term = TermT Id

instance Eq1 TermT   where (==#)      = (==)
instance Ord1 TermT  where compare1   = compare
instance Show1 TermT where showsPrec1 = showsPrec
instance Read1 TermT where readsPrec1 = readsPrec
instance Applicative TermT where pure = Var; (<*>) = ap

instance Monad TermT where
    return = Var

    Var v   >>= f = f v
    Type l  >>= _ = Type l
    App t m >>= f = App (t >>= f) (m >>= f)
    Lam t s >>= f = Lam (t >>= f) (s >>>= f)

lam :: Id -> Term -> Term -> Term
lam v ty t = Lam ty (abstract1Name v t)

-- TODO This assumes that the variables are all distinct, fix that.
branch :: ConId -> [Id] -> Term -> Branch
branch c vars t = Branch c (abstractName (`elemIndex` vars) t)

-- TODO: Define this
-- | Makes all the 'Name's unique
uniquify :: Term -> Term
uniquify = undefined
