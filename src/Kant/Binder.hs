{-# LANGUAGE DeriveFunctor #-}
module Kant.Binder
    ( Binder(..)
    , isBind
    , isWild
    ) where

import           Control.Applicative (Applicative(..))
import           Control.Monad (ap)

-- | Something isomorphic to 'Maybe' for the time being, might change in the
--   future.
data Binder n = Bind n | Wild
    deriving (Show, Eq, Functor)

isBind, isWild :: Binder n -> Bool
isBind (Bind _) = True
isBind Wild     = False
isWild = not . isBind

instance Monad Binder where
    return = Bind

    Bind n >>= f = f n
    Wild   >>= _ = Wild

instance Applicative Binder where
    pure = return
    (<*>) = ap
