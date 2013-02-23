{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Term', due to bound.
module Kant.Environment
    ( Count
    , Env(..)
    , EnvM
      -- * Utilities
    , bumpCount
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

import           Control.Applicative ((<$>))
import           Control.Monad (join, liftM)
import           Prelude hiding (foldr)

import           Control.Monad.Error (MonadError(..))
import           Control.Monad.State (StateT, MonadState(..))
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

type EnvM m = StateT Env m

bumpCount :: Env -> (Count, Env)
bumpCount env@Env{envCount = c} = (c, env{envCount = c+1})

-- | Looks up the type of a variable.
envTy :: Monad m => Tag -> EnvM m (Maybe Term)
envTy v = do Env{envCtx = ctx} <- get
             return (join (fst <$> Map.lookup v ctx))

-- | Looks up the body of a definition.
envDef :: Monad m => Tag -> EnvM m (Maybe Term)
envDef v = do Env{envCtx = ctx} <- get
              return (join (snd <$> Map.lookup v ctx))

envData' :: Monad m => ConId -> EnvM m (Maybe DataBody)
envData' v = do Env{envData = dds} <- get
                return (Map.lookup v dds)

newEnv :: Env
newEnv = Env{ envCtx   = Map.empty
            , envData  = Map.empty
            , envCount = 0
            }

addCtx :: Monad m => Tag -> Maybe Term -> Maybe Term -> EnvM m Bool
addCtx v tym tm =
    do env@Env{envCtx = ctx} <- get
       case Map.lookup v ctx of
           Nothing -> do put env{envCtx = Map.insert v (tym, tm) ctx}
                         return True
           Just _  -> return False

-- | Adds an abstracted variable to an environment, 'Nothing' if the name is
--   already present.
addAbst :: Monad m => Tag -> Term -> EnvM m Bool
addAbst n t = addCtx n (Just t) Nothing

-- | Adds a value definition to an environment, 'Nothing' if the name is already
--   present.
addVal :: Monad m => Tag -> Term -> Term -> EnvM m Bool
addVal v ty t = addCtx v (Just ty) (Just t)

upCtx :: Monad m => Tag -> Maybe Term -> Maybe Term -> EnvM m ()
upCtx v tym tm = do env@Env{envCtx = ctx} <- get
                    put env{envCtx = Map.insert v (tym, tm) ctx}

upAbst :: Monad m => Tag -> Term -> EnvM m ()
upAbst v t = upCtx v (Just t) Nothing

upAbst' :: Monad m => TBinder -> Term -> EnvM m ()
upAbst' Wild        _ = return ()
upAbst' (Bind _ ta) t = upAbst ta t

upVal :: Monad m => Tag -> Term -> Term -> EnvM m ()
upVal v ty t = upCtx v (Just ty) (Just t)

upVal' :: Monad m => TBinder -> Term -> Term -> EnvM m ()
upVal' (Bind _ ta) ty t = upVal ta ty t
upVal' Wild        _  _ = return ()

-- | Adds the type constructors and the data declarations as abstracted variable
--   to an environment, @'Left' n@ if name @n@ is already present.
addData :: (MonadError e m) => ConId -> DataBody -> (ConId -> e) -> EnvM m ()
addData tyc dd@(ParamsT pars (DataT l cons)) err =
    do env₁@Env{envData = dds} <- get
       checkDup tyc env₁
       put env₁{envData = Map.insert tyc dd dds}
       True <- addAbst (toTag tyc) (arrs pars (Type l))
       sequence_ [ do checkDup dc =<< get
                      let allPars = pars ++ pars'
                          parsn ps = zipWith merge ps `liftM`
                                     mapM (\_ -> fresh) [1..length ps]
                      vars₁ <- parsn allPars
                      vars₂ <- parsn pars; vars₃ <- parsn pars'
                      let resTy = app (Var (toTag tyc) : getv vars₁)
                          f     = conFun dc vars₂ vars₃
                      True <- addVal (toTag dc) (arrs vars₁ resTy) f
                      return ()
                 | ConstrT dc (ParamsT pars' Proxy) <- cons ]
  where
    checkDup c Env{envCtx = ctx, envData = dds} =
        if Map.member c dds || Map.member (toTag c) ctx
        then throwError (err c)
        else return ()
    getv = map (\((Bind _ v), _) -> Var v)
    conFun dc vars₁ vars₂ =
        lams (vars₁ ++ vars₂) (Constr dc (getv vars₁) (getv vars₂))
    fresh = do env@Env{envCount = c} <- get
               put env{envCount = c+1}
               return (toTag (show c))
    merge (Wild, ty)         v = (Bind "_" v, ty)
    merge (b@(Bind _ _), ty) _ = (b, ty)
