{-# LANGUAGE DeriveFunctor #-}
module Kant.Name
    ( Name(..)
    , name
    , bound
    , noName
    ) where

import           Data.Monoid (Monoid(..))

data Name f n a
    = Bound n a
    | Free f
    deriving (Show, Functor)

name :: Name n n a -> n
name (Bound n _) = n
name (Free n)    = n

bound :: n -> Name f n n
bound n = Bound n n

noName :: Monoid n => a -> Name f n a
noName ta = Bound mempty ta

instance (Eq a, Eq f) => Eq (Name f n a) where
    Bound _ a == Bound _ b = a  == b
    Free n₁   == Free n₂   = n₁ == n₂
    _         == _         = False

instance (Ord a, Ord f) => Ord (Name f n a) where
    Bound _ a `compare` Bound _ b = compare a b
    Free n₁   `compare` Free n₂   = compare n₁ n₂
    Bound _ _ `compare` Free _    = GT
    Free _    `compare` Bound _ _ = LT
