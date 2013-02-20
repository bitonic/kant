{-# LANGUAGE DeriveFunctor #-}
module Kant.Name
    ( Name(..)
    , name
    , content
    ) where

import           Data.Monoid (Monoid(..))

data Name n a = Name n a
    deriving (Show, Functor)

name :: Name n a -> n
name (Name n _) = n

content :: Name n a -> a
content (Name _ a) = a

instance (Eq a) => Eq (Name n a) where
    Name _ a == Name _ b = a  == b

instance (Ord a) => Ord (Name n a) where
    Name _ a `compare` Name _ b = compare a b

instance Monoid n => Monad (Name n) where
    return = Name mempty
    Name _ a >>= f = f a
