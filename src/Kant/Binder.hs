{-# LANGUAGE DeriveFunctor #-}
module Kant.Binder
    ( Binder(..)
    , isName
    , isWild
    ) where

import           Control.Applicative (Applicative(..))
import           Control.Monad (ap)

-- | Something isomorphic to 'Maybe' for the time being, might change in the
--   future.
data Binder n = Name n | Wild
    deriving (Show, Eq, Functor)

isName, isWild :: Binder n -> Bool
isName (Name _) = True
isName Wild     = False
isWild = not . isName

instance Monad Binder where
    return = Name

    Name n >>= f = f n
    Wild   >>= _ = Wild

instance Applicative Binder where
    pure = return
    (<*>) = ap
