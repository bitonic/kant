module Language.Bertus.Common
    ( (<$>)
    , (<*>)
    , (*>)
    , (<*)
    , (<$)
    ) where

import Control.Monad (liftM, ap)

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
