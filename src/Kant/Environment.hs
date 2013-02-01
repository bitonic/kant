{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Term', due to bound.
module Kant.Environment
    ( ItemT(..)
    , Item
    , CtxT
    , Ctx
    , NestT
    , Nest
    , PullT
    , Pull
    , EnvT(..)
    , Env
      -- * Utilities
    , nestEnv
    , lookupTy
    , lookupDef
    , newEnv
    ) where

import           Control.Applicative ((<$>))
import           Data.Foldable (Foldable)
import           Data.Traversable (Traversable)

import           Bound
import           Bound.Name

import           Kant.Syntax

-- | The inhabitants of our environment
data ItemT a
    = Constr Constr Term        -- ^ Constructor with its type.
    | TyConstr Term [Constr]    -- ^ Type constructor and associated data
                                --   constructors.
    | DeclVal Term Term         -- ^ Declared value, type and value - the value
                                --   will be the 'Var' itself for postulated
                                --   variables.
    | Abstract (TermT a)        -- ^ Abstracted variable, with its type.
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)
type Item = ItemT Id

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
    { envCtx  :: CtxT a
    , envNest :: NestT a
    , envPull :: PullT a
    }
type Env = EnvT Id

-- | To be used when we enter a 'Scope', it adjust the environment functions to
--   work with the new level of boundness.
nestEnv :: EnvT a
        -> EnvT (Var (Name Id b) a)
nestEnv Env{envCtx = ctx, envNest = nest, envPull = pull} =
    Env { envCtx  = \v -> case v of
                              B _  -> Just (Abstract (Var v))
                              F v' -> (F <$>) <$> ctx v'
        , envNest = F . nest
        , envPull = \v -> case v of
                              B b  -> name b
                              F v' -> pull v'
        }

-- | Looks up the type of a variable.
lookupTy :: a -> EnvT a -> Maybe (TermT a)
lookupTy v Env{envCtx = ctx, envNest = nest} =
    case ctx v of
        Nothing              -> Nothing
        Just (Constr _ ty)   -> nest' ty
        Just (TyConstr ty _) -> nest' ty
        Just (DeclVal ty _)  -> nest' ty
        Just (Abstract ty)   -> Just ty
  where nest' ty = Just (nest <$> ty)

-- | Looks up the body of a definition.
lookupDef :: a -> EnvT a -> Maybe (TermT a)
lookupDef v Env{envCtx = ctx, envNest = nest} =
    case ctx v of
        Nothing            -> Nothing
        Just (DeclVal _ t) -> Just (nest <$> t)
        _                  -> Nothing

-- | Creates a new environment given a lookup function for top level
--   declarations.
newEnv :: (Id -> Maybe Item) -> Env
newEnv ctx = Env{envCtx = ctx, envNest = id, envPull = id}
