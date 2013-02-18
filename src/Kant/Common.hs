module Kant.Common
    ( Id
    , ConId
    , Level
    , (!!)
    , elemIndex
    , length
    , splitAt
    , fi
    ) where

import           Control.Applicative ((<$>))
import qualified Data.List as List
import qualified Prelude
import           Prelude hiding ((!!), length, splitAt)

import           Numeric.Natural

type Id = String
type ConId = Id
type Level  = Natural

(!!) :: [a] -> Natural -> a
xs !! i = xs Prelude.!! fromIntegral i

elemIndex :: Eq a => a -> [a] -> Maybe Natural
elemIndex x xs = fromIntegral <$> List.elemIndex x xs

length :: [a] -> Natural
length = fromIntegral . Prelude.length

splitAt :: Natural -> [a] -> ([a], [a])
splitAt i xs = Prelude.splitAt (fromIntegral i) xs

fi :: (Integral a, Num b) => a -> b
fi = fromIntegral
