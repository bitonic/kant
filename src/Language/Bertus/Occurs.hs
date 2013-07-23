module Language.Bertus.Occurs (metas, occurs) where

import Data.Data (Data, Typeable)
import Data.Generics.Schemes (listify)

import Data.Set (Set)
import qualified Data.Set as Set

import Language.Bertus.Tm

type VarMeta v = Either v Meta

metas :: (Data a, Typeable v, Ord v) => a -> Set (VarMeta v)
metas = Set.fromList . listify (const True)

occurs :: (Data a, Typeable v, Ord v) => Head v -> a -> Bool
occurs mv = Set.member mv . metas

data Strength = Weak | Strong
    deriving (Show, Read, Eq, Ord, Data, Typeable)

data Occurrence = Flexible | Rigid Strength
    deriving (Show, Read, Eq, Ord, Data, Typeable)

class Occurs t where
    occurrence :: [Head v] -> t -> Maybe Occurrence
