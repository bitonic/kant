{-# LANGUAGE DeriveFunctor #-}
module Kant.Name
    ( Name(..)
    ) where

data Name f a
    = Bound a
    | Free f
    deriving (Show, Eq, Ord, Functor)
