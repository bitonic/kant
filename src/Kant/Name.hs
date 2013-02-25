{-# LANGUAGE DeriveFunctor #-}
module Kant.Name
    ( Name(..)
    , Tag
    , free
    ) where

import           Numeric.Natural

type Tag = Natural

data Name a
    = Gen Tag a
    | Plain a
    deriving (Show, Eq, Ord, Functor)

free :: a -> Name a
free = Plain