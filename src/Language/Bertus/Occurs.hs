module Language.Bertus.Occurs (metas, occurs) where

import Data.Data (Data)
import Data.Generics.Schemes (listify)

import Data.Set (Set)
import qualified Data.Set as Set

import Language.Bertus.Tm

metas :: Data a => a -> Set Meta
metas = Set.fromList . listify (const True)

occurs :: Data a => Meta -> a -> Bool
occurs mv = Set.member mv . metas
