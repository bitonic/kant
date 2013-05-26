{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module Kant.Monad.Base
    ( KMonadT
    , KMonadP
    , KMonadE
    , KMonad(KMonad)
    , runKMonad
    , mapKMonad
    , fromKMonadP
    , throwKError
    , getEnv
    , putEnv
    , restoreEnv
    , nestM
    , nestPM
    , freshRef
    ) where

import           Control.Applicative (Applicative)
import           Control.Arrow (second)

import           Control.Monad.Error (ErrorT(..), mapErrorT, throwError)
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.State (StateT(..), mapStateT, put, get)
import           Control.Monad.Trans.Class (MonadTrans(..))

import           Bound
import           Data.Proxy

import           Kant.Common
import           Kant.Cursor
import           Kant.Env
import           Kant.Error
import           Kant.Term

newtype KMonad f v m a = KMonad {runKMonad' :: StateT (f v) (ErrorT KError m) a}
    deriving (Functor, Applicative, Monad)
type KMonadP = KMonad (Env Proxy)
type KMonadT = KMonad (Env TmRef)
type KMonadE f = KMonad (Env f)

instance MonadTrans (KMonad f v) where
    lift m = KMonad (lift (lift m))

instance MonadIO m => MonadIO (KMonad f v m) where
    liftIO = KMonad . liftIO

runKMonad :: f v -> KMonad f v m a -> m (Either KError (a, f v))
runKMonad env = runErrorT . (`runStateT` env) . runKMonad'

mapKMonad :: (m (Either KError (a, f v)) -> n (Either KError (b, f v)))
          -> KMonad f v m a -> KMonad f v n b
mapKMonad f = KMonad . mapStateT (mapErrorT f) . runKMonad'

fromKMonadP :: (IsCursor c, Monad m) => KMonad (c Proxy) v m a -> KMonad (c f) v m a
fromKMonadP (KMonad (StateT f)) =
    KMonad $ StateT $ \env -> second (restoreC env) <$> f (toP env)

throwKError :: Monad m => KError -> KMonad f v m a
throwKError = KMonad . throwError

getEnv :: Monad m => KMonad f v m (f v)
getEnv = KMonad get

putEnv :: Monad m => f v -> KMonad f v m ()
putEnv env = KMonad (put env)

restoreEnv :: Monad m => KMonad f v m a -> KMonad f v m a
restoreEnv m = do env <- getEnv; x <- m; putEnv env; return x

-- | Enters a scope with a certain value and type, runs an action on that new
--   scope, and returns back to the outer scope.
nestM :: (Monad m, IsCursor c, Functor f)
      => f v -> KMonad (c f) (Var NameId v) m a -> KMonad (c f) v m a
nestM ty (KMonad m) =
    KMonad (StateT (\env -> second (restoreC env) <$> runStateT m (nestC env ty)))

nestPM :: (Monad m, IsCursor c)
       => KMonad (c Proxy) (Var NameId v) m a -> KMonad (c Proxy) v m a
nestPM = nestM Proxy

freshRef :: (Monad m) => KMonadE f v m Ref
freshRef = do env <- getEnv; envRef env <$ putEnv (env{envRef = envRef env + 1})
