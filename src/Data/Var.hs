module Data.Var (Var(..), nest, toMaybe) where

import Data.Traversable
import Data.Foldable
import Data.Data (Data, Typeable)

data Var a v = B a | F v
    deriving (Show, Functor, Foldable, Traversable, Data, Typeable)

instance Eq v => Eq (Var a v) where
    B _  == B _  = True
    F v1 == F v2 = v1 == v2
    _    == _    = False

instance Ord v => Ord (Var a v) where
    compare (B _ ) (B _ ) = EQ
    compare (F v1) (F v2) = compare v1 v2
    compare (B _ ) (F _ ) = LT
    compare (F _ ) (B _ ) = GT

nest :: Functor t => t v -> t (Var a v)
nest = fmap F

toMaybe :: Var a v -> Maybe v
toMaybe (B _) = Nothing
toMaybe (F v) = Just v
