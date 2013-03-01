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
    , app
      -- * Smart destructors
    , AppV(..)
    , appV
    , appHead
    , binding
    , bindingN
    , scopeV
    , scopeN
    , arrLen
    ) where

import           Control.Applicative ((<$>))
import           Data.Foldable (Foldable)
import           Data.Traversable (Traversable)

import           Bound
import           Bound.Name
import           Bound.Scope
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
    | Canon ConId [Term v]
    | Elim ConId [Term v]
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

type TermId = Term Id

instance Eq1 Term   where (==#)      = (==)
instance Ord1 Term  where compare1   = compare
instance Show1 Term where showsPrec1 = showsPrec
instance Read1 Term where readsPrec1 = readsPrec

instance Monad Term where
    return = V

    V v        >>= f = f v
    Ty         >>= _ = Ty
    Lam ab     >>= f = Lam (subAb ab f)
    Arr ab     >>= f = Arr (subAb ab f)
    App t₁ t₂  >>= f = App (t₁ >>= f) (t₂ >>= f)
    Canon c ts >>= f = Canon c (map (>>= f) ts)
    Elim c ts  >>= f = Elim c (map (>>= f) ts)

data Abs v = Abs (Term v) (Scope (NameId ()) Term v)
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

subAb :: Abs a -> (a -> Term b) -> Abs b
subAb (Abs t s) f = Abs (t >>= f) (s >>>= f)

abs_ :: Id -> TermId -> TermId -> Abs Id
abs_ v t₁ t₂ =  Abs t₁ (abstract1Name v t₂)

lam, arr :: Id -> TermId -> TermId -> TermId
lam v t = Lam . abs_ v t
arr v t = Arr . abs_ v t

app :: [Term v] -> Term v
app = foldl1 App

data AppV v = AppV (Term v) [Term v]

appV :: Term v -> AppV v
appV (App t₁ t₂) = AppV t (ts ++ [t₂])
  where AppV t ts = appV t₁
appV t = AppV t []

appHead :: Term v -> Term v
appHead (appV -> AppV t _) = t

binding :: Scope (NameId ()) Term v -> Maybe (NameId ())
binding s = case bindings s of
                []      -> Nothing
                (n : _) -> Just n

bindingN :: Scope (NameId ()) Term v -> NameId ()
bindingN s = case bindings s of
                 []      -> Name "$" ()
                 (n : _) -> n

scopeV :: Scope (NameId ()) Term v -> (NameId () -> Term v)
       -> (Maybe (NameId ()), Term v)
scopeV s f =
    case bindings s of
        []      -> (Nothing, instantiate1 (error "scopeV: the impossible happened") s)
        (n : _) -> (Just n, instantiate1 (f n) s)

scopeN :: Scope (NameId ()) Term Id -> (Maybe Id, TermId)
scopeN s = (name <$> mn, t) where (mn, t) = scopeV s (\(Name n _) -> V n)

arrLen :: Term v -> Int
arrLen (Arr (Abs _ s)) = 1 + arrLen (fromScope s)
arrLen _               = 0