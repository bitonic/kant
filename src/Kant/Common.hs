module Kant.Common
    ( trim
    , (<$>)
    , (<*>)
    , (*>)
    , (<*)
    , (<$)
    ) where

import           Control.Monad (liftM, ap)
import           Data.Char (isSpace)

trim :: String -> String
trim = reverse . f . reverse . f where f = dropWhile isSpace

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
