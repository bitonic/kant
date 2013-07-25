{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Dummy (Dummy(..)) where

import Data.Data (Data, Typeable)
import Data.Foldable (Foldable)
import Data.Monoid (Monoid)
import Data.Traversable (Traversable)

newtype Dummy a = Dummy {unDummy :: a}
    deriving (Show, Functor, Foldable, Traversable, Data, Typeable, Monoid)

instance Eq (Dummy a) where
    _ == _ = True

instance Ord (Dummy a) where
    _ `compare` _ = EQ
