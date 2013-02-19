module Kant.Common
    ( Id
    , ConId
    , Level
    , (!!)
    , elemIndex
    , length
    , splitAt
    , drop
    , fi
    ) where

import           Control.Applicative ((<$>))
import qualified Data.List as List
import qualified Prelude
import           Prelude hiding ((!!), length, splitAt, drop)

import           Numeric.Natural

type Id = String
type ConId = Id
type Level  = Natural

(!!) :: [a] -> Natural -> a
xs !! i = xs Prelude.!! fi i

elemIndex :: Eq a => a -> [a] -> Maybe Natural
elemIndex x xs = fi <$> List.elemIndex x xs

length :: [a] -> Natural
length = fi . Prelude.length

splitAt :: Natural -> [a] -> ([a], [a])
splitAt i xs = Prelude.splitAt (fi i) xs

drop :: Natural -> [a] -> [a]
drop i = Prelude.drop (fi i)

fi :: (Integral a, Num b) => a -> b
fi = fromIntegral