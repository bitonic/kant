module Language.Bertus.Common
    ( (<$>)
    , (<*>)
    , (*>)
    , (<*)
    , (<$)
    , mapMaybeMonotonic
    ) where

import Control.Monad (liftM, ap)
import Data.Maybe (isJust, fromMaybe)

import Data.Set (Set)
import qualified Data.Set as Set

#include "../../impossible.h"

infixl 4 <$>, <*>, <*, *>

(<$>) :: Monad m => (a -> b) -> m a -> m b
(<$>) = liftM

(<*>) :: Monad m => m (a -> b) -> m a -> m b
(<*>) = ap

(<*) :: Monad m => m a -> m b -> m a
a <* b = do x <- a; b; return x

(*>) :: Monad m => m a -> m b -> m b
(*>) = (>>)

(<$) :: Monad m => a -> m b -> m a
(<$) = liftM . const

-- | Invariant: the @f@ provided must respect the law
--
--   @(f x = Just x' /\ f y = Just y' /\ x <= y) ==> x' <= y'@
--
--   For all @x, y :: a@.  The function converting to Maybe is assumed
--   to be cheap, since it is ran twice.
mapMaybeMonotonic :: (a -> Maybe b) -> Set a -> Set b
mapMaybeMonotonic f =
    Set.mapMonotonic (fromMaybe IMPOSSIBLE("We removed all the Nothing") . f) .
    Set.filter (isJust . f)

