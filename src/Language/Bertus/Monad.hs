{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.Bertus.Monad
    ( BError
    , BMonadT(..)
    , BMonadBwdT
    , BMonadListT
    , runBMonadT
    , nestBwd
    , toCtxBwdM
    , lookupVar
    , lookupMeta
    , pushL
    , pushR
    , putL
    , putR
    , popL
    , popR
    , goL
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
import Language.Bertus.Tm

type BError = String

newtype BMonadT pars v m a =
    BMonadT {unBMonadT :: StateT (Context pars v) (FreshT (ErrorT BError m)) a}
    deriving (Functor, Applicative, Monad, MonadState (Context pars v),
              MonadError BError, MonadFresh)

type BMonadBwdT = BMonadT ParamBwd
type BMonadListT v = BMonadT (ParamList v) v

instance MonadTrans (BMonadT pars v) where
    lift = BMonadT . lift . lift . lift

runBMonadT :: Monad m
           => Context pars v -> BMonadT pars v m a
           -> m (Either BError (a, Context pars v))
runBMonadT ctx (BMonadT m) = runErrorT (runFreshT (runStateT m ctx))

-- TODO Here we *throw away* new Metas.  This can't be right, but there
-- isn't an easy solution.  Investigate on what to do.
nestBwd :: Monad m
        => Param v -> BMonadBwdT (Var Name v) m a -> BMonadBwdT v m a
nestBwd ty (BMonadT m) =
    BMonadT $ StateT $ \ctx ->
    second (const ctx) <$> runStateT m (nestCtxBwd ty ctx)

toCtxBwdM :: (Ord v, Monad m) => BMonadBwdT v m b -> BMonadListT v m b
toCtxBwdM m =
    do ctx <- get
       res <- lift (runBMonadT (toCtxBwd ctx) m)
       case res of
           Left err     -> throwError err
           Right (x, _) -> return x

lookupVar :: Monad m
          => (a -> Context pars v -> Maybe (Param v))
          -> a -> Twin -> BMonadT pars v m (Ty v)
lookupVar f v tw =
    do ctx <- get
       case (f v ctx, tw) of
           (Just (Param ty     ), Only ) -> return ty
           (Just (Twins tyl _  ), TwinL) -> return tyl
           (Just (Twins _   tyr), TwinR) -> return tyr
           (Just _,               _    ) -> throwError "evil twin"
           (Nothing,              _    ) -> throwError "out of bounds"

lookupMeta :: Monad m => Meta -> BMonadT pars v m (Ty v)
lookupMeta mv = go =<< gets ctxLeft
  where
    go :: Monad m => ContextL v -> BMonadT pars v m (Ty v)
    go B0 = throwError ("missing metavariable " ++ show mv)
    go (_  :< Entry mv' ty _) | mv == mv' = return ty
    go (bw :< _             )             = go bw

modifyL :: Monad m => (ContextL v -> ContextL v) -> BMonadT pars v m ()
modifyL f = do ctx@Context{ctxLeft = ctxL} <- get
               put ctx{ctxLeft = f ctxL}

modifyR :: Monad m => (ContextR v -> ContextR v) -> BMonadT pars v m ()
modifyR f = do ctx@Context{ctxRight = ctxR} <- get
               put ctx{ctxRight = f ctxR}


pushL :: Monad m => Entry v -> BMonadT pars v m ()
pushL entry = modifyL (:< entry)

pushR :: Monad m => Either (Subs v) (Entry v) -> BMonadT pars v m ()
pushR entry = modifyR (entry :)

putL :: Monad m => ContextL v -> BMonadT pars v m ()
putL x = modifyL (const x)

putR :: Monad m => ContextR v -> BMonadT pars v m ()
putR x = modifyR (const x)

popL :: Monad m => BMonadT pars v m (Entry v)
popL = do ctxL <- gets ctxLeft
          case ctxL of
              (ctxL' :< entry) -> entry <$ putL ctxL'
              B0               -> error "popL ran out of context"

popR :: Monad m => BMonadT pars v m (Maybe (Either (Subs v) (Entry v)))
popR = do ctxR <- gets ctxRight
          case ctxR of
              (x  : ctxR') -> Just x <$ putR ctxR'
              []           -> return Nothing

goL :: Monad m => BMonadT pars v m ()
goL = popL >>= pushR . Right
