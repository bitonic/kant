{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.Term
    ( Id
    , ConId
    , NameId
    , Term(..)
    , TermId
    , Abs(..)
      -- * Smart constructors
    , lam
    , arr
      -- * Smart destructors
    , AppV(..)
    , appV
    , appHead
    ) where

import           Data.Foldable (Foldable)
import           Data.Traversable (Traversable)

import           Bound
import           Bound.Name
import           Prelude.Extras

type Id = String
type ConId = Id
type NameId = Name Id

data Term v
    = V v
    | Ty
    | Lam (Abs v)
    | Arr (Abs v)
    | App (Term v) (Term v)
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

type TermId = Term Id

instance Eq1 Term   where (==#)      = (==)
instance Ord1 Term  where compare1   = compare
instance Show1 Term where showsPrec1 = showsPrec
instance Read1 Term where readsPrec1 = readsPrec

instance Monad Term where
    return = V

    V v       >>= f = f v
    Ty        >>= _ = Ty
    Lam ab    >>= f = Lam (subAb ab f)
    Arr ab    >>= f = Arr (subAb ab f)
    App t₁ t₂ >>= f = App (t₁ >>= f) (t₂ >>= f)

data Abs v = Abs (Term v) (Scope (NameId ()) Term v)
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

subAb :: Abs a -> (a -> Term b) -> Abs b
subAb (Abs t s) f = Abs (t >>= f) (s >>>= f)

abs_ :: Id -> Term Id -> Term Id -> Abs Id
abs_ v t₁ t₂ =  Abs t₁ (abstract1Name v t₂)

lam, arr :: Id -> Term Id -> Term Id -> Term Id
lam v t = Lam . abs_ v t
arr v t = Arr . abs_ v t

data AppV v = AppV (Term v) [Term v]

appV :: Term v -> AppV v
appV (App t₁ t₂) = AppV t (ts ++ [t₂])
  where AppV t ts = appV t₁
appV t = AppV t []

appHead :: Term v -> Term v
appHead (appV -> AppV t _) = t

