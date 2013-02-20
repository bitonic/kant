{-# LANGUAGE DeriveFunctor #-}
module Kant.Binder
    ( Binder(..)
    , isBind
    , isWild
    , fromBinder
    ) where

import           Control.Applicative (Applicative(..))
import           Control.Monad (ap, MonadPlus(..))

-- | Something isomorphic to 'Maybe' for the time being, might change in the
--   future.
data Binder n = Bind n | Wild
    deriving (Show, Eq, Functor)

isBind, isWild :: Binder n -> Bool
isBind (Bind _) = True
isBind Wild     = False
isWild = not . isBind

fromBinder :: n -> Binder n -> n
fromBinder x Wild     = x
fromBinder _ (Bind x) = x

instance Monad Binder where
    return = Bind

    Bind n >>= f = f n
    Wild   >>= _ = Wild

instance Applicative Binder where
    pure = return
    (<*>) = ap

instance MonadPlus Binder where
    mzero = Wild

    Wild `mplus` b    = b
    b    `mplus` Wild = b
    b    `mplus` _    = b
