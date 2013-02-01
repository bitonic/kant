{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
-- | Sets up a warm place (cit) to reduce, typecheck, and "reify" things into.
--   The main hurdle is the multi-level structure of our 'Term', due to bound.
module Kant.Environment
    ( ItemT(..)
    , CtxT
    , Ctx
    , NestT
    , Nest
    , PullT
    , Pull
    , EnvT(..)
    , Env
    , nestEnv
    ) where

import           Control.Applicative ((<$>))
import           Data.Foldable (Foldable)
import           Data.Traversable (Traversable)

import           Bound
import           Bound.Name

import           Kant.Syntax

-- | The inhabitants of our environment
data ItemT a
    = Constr Constr Term        -- ^ Constructor with its type
    | TyConstr Term [Constr]    -- ^ Type constructor and associated data
                                --   constructors
    | DeclVal Term Term         -- ^ Declared value, type value - the value will
                                --   be the 'Var' itself for postulated
                                --   variables.
    | Bound (TermT a)           -- ^ Bound variable, with its type
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

-- | Given a bound name, returns the matching 'ItemT', if present.
type CtxT a = (a -> Maybe (ItemT a))
type Ctx = CtxT Id

-- | Nests an 'Id' the required amount of times to turn it into the correct type
--   to be put in some @'TermT' a@.
type NestT a = Id -> a
type Nest = NestT Id

-- | Extracts the name out of the bound variable, useful to print out nested
--   terms.
type PullT a = a -> Id
type Pull = PullT Id

-- | Bringing it all together
data EnvT a = Env
    { stCtx  :: CtxT a
    , stNest :: NestT a
    , stPull :: PullT a
    }
type Env = EnvT Id

-- | To be used when we enter a 'Scope', it adjust the environment functions to
--   work with the new level of boundness.
nestEnv :: EnvT a
        -> (b -> TermT a)       -- ^ Function that substitutes the variables of
                                --   the scope we are entering, same as the one
                                --   accepted by 'instantiateName' & co.
        -> EnvT (Var (Name Id b) a)
nestEnv Env{stCtx = ctx, stNest = nest, stPull = pull} f =
    Env { stCtx  = \v -> case v of
                             B (Name _ b) -> Just (F <$> Bound (f b))
                             F v'         -> (F <$>) <$> ctx v'
        , stNest = F . nest
        , stPull = \v -> case v of
                             B b  -> name b
                             F v' -> pull v'
        }
