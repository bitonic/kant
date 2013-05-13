{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Data.Bwd (Bwd(..), toList) where

import           Data.Foldable (Foldable, toList)
import           Data.Monoid (Monoid(..))
import           Data.Traversable (Traversable)

data Bwd a = B0 | Bwd a :< a
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance Monoid (Bwd a) where
    mempty = B0

    xs `mappend` B0        = xs
    xs `mappend` (ys :< y) = (xs `mappend` ys) :< y
