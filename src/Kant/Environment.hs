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
    , bumpCount
    , freshTag
    , freshId
    , envTy
    , envDef
    , envData'
    , newEnv
    , addAbst
    , addVal
    , upAbst
    , upAbst'
    , upVal
    , upVal'
    , addData
    ) where

import           Control.Applicative ((<$>), Applicative)
import           Control.Monad (join, liftM)
import           Prelude hiding (foldr)

import           Control.Monad.Error (MonadError(..))
import           Control.Monad.State (StateT(..), MonadState(..))
import           Control.Monad.Error (Error(..), ErrorT)
import           Data.Map (Map)
import qualified Data.Map as Map

import           Kant.Term

type Item = (Maybe Term, Maybe Term)

type Count = Integer

-- | Bringing it all together
data Env = Env
    { envCtx   :: Map Tag Item
    , envData  :: Map ConId DataBody
    , envCount :: Count
    }

class (Functor m, Applicative m, MonadState Env m) => MonadEnv m
instance (Functor m, Applicative m, Monad m) => MonadEnv (StateT Env m)
instance (Functor m, Applicative m, Monad m, Error e) =>
         MonadEnv (ErrorT e (StateT Env m))

runEnv :: Env -> StateT Env m a -> m (a, Env)
runEnv env (StateT f) = f env

bumpCount :: MonadEnv m => m Count
bumpCount = do env@Env{envCount = c} <- get
               put env{envCount = c+1}
               return c

freshTag :: MonadEnv m => m Tag
freshTag = (toTag . show) `liftM` bumpCount

freshId :: MonadEnv m => m Id
freshId = show `liftM` bumpCount

-- | Looks up the type of a variable.
envTy :: MonadEnv m => Tag -> m (Maybe Term)
envTy v = do Env{envCtx = ctx} <- get
             return (join (fst <$> Map.lookup v ctx))

-- | Looks up the body of a definition.
envDef :: MonadEnv m => Tag -> m (Maybe Term)
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

addCtx :: MonadEnv m => Tag -> Maybe Term -> Maybe Term -> m Bool
addCtx v tym tm =
    do env@Env{envCtx = ctx} <- get
       case Map.lookup v ctx of
           Nothing -> do put env{envCtx = Map.insert v (tym, tm) ctx}
                         return True
           Just _  -> return False

-- | Adds an abstracted variable to an environment, 'Nothing' if the name is
--   already present.
addAbst :: MonadEnv m => Tag -> Term -> m Bool
addAbst n t = addCtx n (Just t) Nothing

-- | Adds a value definition to an environment, 'Nothing' if the name is already
--   present.
addVal :: MonadEnv m => Tag -> Term -> Term -> m Bool
addVal v ty t = addCtx v (Just ty) (Just t)

upCtx :: MonadEnv m => Tag -> Maybe Term -> Maybe Term -> m ()
upCtx v tym tm = do env@Env{envCtx = ctx} <- get
                    put env{envCtx = Map.insert v (tym, tm) ctx}

upAbst :: MonadEnv m => Tag -> Term -> m ()
upAbst v t = upCtx v (Just t) Nothing

upAbst' :: MonadEnv m => TBinder -> Term -> m ()
upAbst' Wild        _ = return ()
upAbst' (Bind _ ta) t = upAbst ta t

upVal :: MonadEnv m => Tag -> Term -> Term -> m ()
upVal v ty t = upCtx v (Just ty) (Just t)

upVal' :: MonadEnv m => TBinder -> Term -> Term -> m ()
upVal' (Bind _ ta) ty t = upVal ta ty t
upVal' Wild        _  _ = return ()

-- | Adds the type constructors and the data declarations as abstracted variable
--   to an environment, @'Left' n@ if name @n@ is already present.
addData :: (MonadError e m, MonadEnv m)
        => ConId -> DataBody -> (ConId -> e) -> m ()
addData tyc dd@(Tele pars (DataT l cons)) err =
    do env₁@Env{envData = dds} <- get
       checkDup tyc env₁
       put env₁{envData = Map.insert tyc dd dds}
       True <- addAbst (toTag tyc) (arrs pars (Type l))
       sequence_ [ do checkDup dc =<< get
                      let allPars = pars ++ pars'
                          parsn ps = zipWith merge ps `liftM`
                                     mapM (\_ -> freshTag) [1..length ps]
                      vars₁ <- parsn allPars
                      vars₂ <- parsn pars; vars₃ <- parsn pars'
                      let resTy = app (Var (toTag tyc) :
                                       getv (take (length pars) vars₁))
                          f     = conFun dc vars₂ vars₃
                      True <- addVal (toTag dc) (arrs vars₁ resTy) f
                      return ()
                 | ConstrT dc (Tele pars' Proxy) <- cons ]
  where
    checkDup c Env{envCtx = ctx, envData = dds} =
        if Map.member c dds || Map.member (toTag c) ctx
        then throwError (err c)
        else return ()
    getv = map (\((Bind _ v), _) -> Var v)
    conFun dc vars₁ vars₂ =
        lams (vars₁ ++ vars₂) (Constr dc (getv vars₁) (getv vars₂))
    merge (Wild, ty)         v = (Bind "_" v, ty)
    merge (b@(Bind _ _), ty) _ = (b, ty)
