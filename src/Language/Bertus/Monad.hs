{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.Bertus.Monad
    ( BError
    , BMonadT(..)
    , runBMonadT
    , nestM
    , lookupVar
    , lookupMeta
    , module Control.Monad.Error
    , module Control.Monad.State
    , module Control.Monad.Fresh
    ) where

import Control.Applicative (Applicative)
import Control.Arrow (second)

import Control.Monad.Error
import Control.Monad.State

import Control.Monad.Fresh
import Data.Bwd
import Data.Var
import Language.Bertus.Common
import Language.Bertus.Context
import Language.Bertus.Tele
import Language.Bertus.Tm

type BError = String

newtype BMonadT v m a =
    BMonadT {unBMonadT :: StateT (Context v) (FreshT (ErrorT BError m)) a}
    deriving (Functor, Applicative, Monad, MonadState (Context v),
              MonadError BError, MonadFresh)

instance MonadTrans (BMonadT v) where
    lift = BMonadT . lift . lift . lift

runBMonadT :: Monad m
           => Context v -> BMonadT v m a -> m (Either BError (a, Context v))
runBMonadT ctx (BMonadT m) = runErrorT (runFreshT (runStateT m ctx))

nestM :: Monad m => Param v -> BMonadT (Var Name v) m a -> BMonadT v m a
nestM ty (BMonadT m) =
    BMonadT $ StateT $ \ctx ->
    second (const ctx) <$> runStateT m (nestCtx ty ctx)

lookupVar :: Monad m => v -> Twin -> BMonadT v m (Ty v)
lookupVar v tw =
    do Context{ctxParams = pars} <- get
       case (lookupBwd pars v, tw) of
           (Just (Param ty     ), Only ) -> return ty
           (Just (Twins tyl _  ), TwinL) -> return tyl
           (Just (Twins _   tyr), TwinR) -> return tyr
           (Just _,               _    ) -> throwError "evil twin"
           (Nothing,              _    ) -> throwError "out of bounds"

lookupMeta :: Monad m => Meta -> BMonadT v m (Ty v)
lookupMeta mv = go =<< gets ctxLeft
  where
    go :: Monad m => ContextL v -> BMonadT v m (Ty v)
    go B0 = throwError ("missing metavariable " ++ show mv)
    go (_  :< Entry mv' ty _) | mv == mv' = return ty
    go (bw :< _             )             = go bw
