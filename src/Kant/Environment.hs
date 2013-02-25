{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Term', due to bound.
module Kant.Environment
    ( Count
    , Env(..)
    , MonadEnv
    , runEnv
      -- * Utilities
    , envTy
    , envDef
    , envData'
    , newEnv
    , addAbst
    , addVal
    , upAbst
    , upVal
    , delCtx
    , addData
    ) where

import           Control.Applicative ((<$>), Applicative)
import           Control.Monad (join)
import           Data.List (inits)

import           Control.Monad.Error (Error(..), ErrorT)
import           Control.Monad.Error (MonadError(..))
import           Control.Monad.State (StateT(..), MonadState(..))
import           Control.Monad.Trans (lift)
import           Data.Map (Map)
import qualified Data.Map as Map

import           Kant.Name
import           Kant.Term

type Item = (Maybe Term, Maybe Term)

type Count = Tag

-- | Bringing it all together
data Env = Env
    { envCtx   :: Map TName Item
    , envData  :: Map ConId DataBody
    , envCount :: Count
    }

class (Functor m, Applicative m, MonadState Env m, MonadSubst m) => MonadEnv m

instance (Functor m, Applicative m, Monad m) => MonadSubst (StateT Env m) where
    fresh v = do env@Env{envCount = c} <- get
                 put env{envCount = c+1}
                 return $ case v of
                              Plain n -> Gen c n
                              Gen _ n -> Gen c n

instance (Functor m, Applicative m, Monad m) => MonadEnv (StateT Env m)

instance (Functor m, Applicative m, Monad m, Error e) =>
         MonadSubst (ErrorT e (StateT Env m)) where
    fresh v = lift (fresh v)

instance (Functor m, Applicative m, Monad m, Error e) =>
         MonadEnv (ErrorT e (StateT Env m))

runEnv :: Env -> StateT Env m a -> m (a, Env)
runEnv env (StateT f) = f env

-- | Looks up the type of a variable.
envTy :: MonadEnv m => TName -> m (Maybe Term)
envTy v = do Env{envCtx = ctx} <- get
             return (join (fst <$> Map.lookup v ctx))

-- | Looks up the body of a definition.
envDef :: MonadEnv m => TName -> m (Maybe Term)
envDef v = do Env{envCtx = ctx} <- get
              return (join (snd <$> Map.lookup v ctx))

envData' :: MonadEnv m => ConId -> m (Maybe DataBody)
envData' v = do Env{envData = dds} <- get
                return (Map.lookup v dds)

newEnv :: Env
newEnv = Env{ envCtx   = Map.empty
            , envData  = Map.empty
            , envCount = 0
            }

addCtx :: MonadEnv m => TName -> Maybe Term -> Maybe Term -> m Bool
addCtx v tym tm =
    do env@Env{envCtx = ctx} <- get
       case Map.lookup v ctx of
           Nothing -> do put env{envCtx = Map.insert v (tym, tm) ctx}
                         return True
           Just _  -> return False

-- | Adds an abstracted variable to an environment, 'Nothing' if the name is
--   already present.
addAbst :: MonadEnv m => TName -> Term -> m Bool
addAbst n t = addCtx n (Just t) Nothing

-- | Adds a value definition to an environment, 'Nothing' if the name is already
--   present.
addVal :: MonadEnv m => TName -> Term -> Term -> m Bool
addVal v ty t = addCtx v (Just ty) (Just t)

upCtx :: MonadEnv m => TName -> Maybe Term -> Maybe Term -> m ()
upCtx v tym tm = do env@Env{envCtx = ctx} <- get
                    put env{envCtx = Map.insert v (tym, tm) ctx}

upAbst :: MonadEnv m => TName -> Term -> m ()
upAbst v t = upCtx v (Just t) Nothing

upVal :: MonadEnv m => TName -> Term -> Term -> m ()
upVal v ty t = upCtx v (Just ty) (Just t)

delCtx :: MonadEnv m => TName -> m ()
delCtx v = do env@Env{envCtx = ctx} <- get
              put env{envCtx = Map.delete v ctx}

-- | Adds the type constructors and the data declarations as abstracted variable
--   to an environment, @'Left' n@ if name @n@ is already present.
addData :: (MonadError e m, MonadEnv m)
        => ConId -> DataBody -> (ConId -> e) -> m ()
addData tyc dd@(Tele typars₁ (DataT l cons)) err =
    -- TODO here we manipulate things and build up terms, but do we avoid name
    -- capturing?  I think it's better to refresh all variables.
    do env₁@Env{envData = dds} <- get
       checkDup tyc env₁
       put env₁{envData = Map.insert tyc dd dds}
       True <- addAbst (free tyc) (pis typars₁ (Type l))
       typars₂ <- mapM freshV typars₁
       let tybs = zip (map fst typars₁) (getV typars₂)
       typars₃ <- sequence [ (b,) <$> substManyB bs ty
                           | ((b, ty), bs) <- zip typars₂ (inits tybs) ]
       sequence_ [ do checkDup dc =<< get
                      dpars₂ <- mapM freshV dpars₁
                      dpars₃ <- sequence [ (b,) <$> substManyB tybs ty
                                         | (b, ty) <- dpars₂ ]
                      let resTy = app (Var (free tyc) : getV typars₃)
                          f     = conFun dc typars₃ dpars₂
                      True <- addVal (free dc) (pis (typars₃ ++ dpars₃) resTy) f
                      return ()
                 | ConstrT dc (Tele dpars₁ Proxy) <- cons ]
  where
    checkDup c Env{envCtx = ctx, envData = dds} =
        if Map.member c dds || Map.member (free c) ctx
        then throwError (err c)
        else return ()
    getV = map (Var . fst)
    conFun dc typars dpars =
        lams (typars ++ dpars) (Constr dc (getV typars) (getV dpars))
    freshV (v, ty) = (,ty) <$> fresh v
