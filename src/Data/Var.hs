module Data.Var (Var(..), nest, toMaybe, dummy) where

import Data.Data (Data, Typeable)
import Data.Foldable (Foldable)
import Data.Monoid (Monoid, mempty)
import Data.Traversable (Traversable)

data Var a v = B a | F v
    deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Data, Typeable)

nest :: Functor t => t v -> t (Var a v)
nest = fmap F

toMaybe :: Var a v -> Maybe v
toMaybe (B _) = Nothing
toMaybe (F v) = Just v

dummy :: Monoid a => Var a v
dummy = B mempty
