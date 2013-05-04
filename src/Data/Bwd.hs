{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Data.Bwd (Bwd(..), toList, bmap) where

import           Data.Foldable (Foldable, toList)
import           Data.Traversable (Traversable, mapM)

import           Control.Monad.Identity (runIdentity)

data Bwd a = B0 | Bwd a :< a
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

bmap :: (a -> b) -> Bwd a -> Bwd b
bmap f = runIdentity . Data.Traversable.mapM (return . f)
