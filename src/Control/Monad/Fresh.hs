{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Control.Monad.Fresh (Ref, FreshT, runFreshT) where

import Control.Monad.Cont
import Control.Monad.Error
import Control.Monad.List
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

newtype Ref = Ref Integer
    deriving (Show, Eq, Ord)

newtype FreshT m a = FreshT {unFreshT :: StateT Integer m a}

runFreshT :: Monad m => FreshT m a -> m a
runFreshT (FreshT m) = evalStateT m 0

class MonadFresh m where
    fresh :: m Ref

instance Monad m => Monad (FreshT m) where
    return = FreshT . return
    FreshT m >>= f = FreshT (m >>= unFreshT . f)

instance Monad m => MonadFresh (FreshT m) where
    fresh = FreshT $
            do c <- get
               put (c + 1)
               return (Ref c)

instance MonadTrans FreshT where
    lift = FreshT . lift

-- In

instance (Monad m, MonadFresh m) => MonadFresh (StateT s m) where
    fresh = lift fresh

instance (Monad m, MonadFresh m) => MonadFresh (ReaderT r m) where
    fresh = lift fresh

instance (Monad m, Monoid w, MonadFresh m) => MonadFresh (WriterT w m) where
    fresh = lift fresh

instance (Monad m, MonadFresh m) => MonadFresh (ListT m) where
    fresh = lift fresh

instance (Monad m, Error e, MonadFresh m) => MonadFresh (ErrorT e m) where
    fresh = lift fresh

instance (Monad m, MonadFresh m) => MonadFresh (ContT r m) where
    fresh = lift fresh

-- Out

instance (Monad m, MonadState s m) => MonadState s (FreshT m) where
    get   = lift get
    put   = lift . put
    state = lift . state

instance (Monad m, MonadReader r m) => MonadReader r (FreshT m) where
    ask     = FreshT ask
    local f = FreshT . local f . unFreshT

instance (Monad m, MonadWriter w m) => MonadWriter w (FreshT m) where
    writer = FreshT . writer
    tell   = FreshT . tell
    listen = FreshT . listen . unFreshT
    pass   = FreshT . pass . unFreshT

instance (Monad m, MonadError e m) => MonadError e (FreshT m) where
    throwError = FreshT . throwError
    catchError (FreshT m) f = FreshT (catchError m (unFreshT . f))
