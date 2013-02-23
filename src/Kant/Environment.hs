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
    ) where

import           Control.Applicative ((<$>))
import           Control.Monad (join)
import           Prelude hiding (foldr)

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

-- -- | Extracts the types out of a data declaration.
-- --
-- --   A type function will be generated as type constructor, taking the
-- --   parameters as arguments and returning someting of @Type l@, where @l@ is
-- --   the level specified in the declaration.
-- --
-- --   Another function will be generated for each data constructor, taking all
-- --   the parameters of the type constructor plus its own parameter.
-- dataDecl :: Data -> ((Id, Item), [(Id, Item)])
-- dataDecl (Data c pars l cons) =
--     ((c, (Just (arrs pars (Type l)), Nothing)), cons')
--   where
--     cons' = [(c', (Just (resTy pars'), Just (conFun c' pars'))) | (c', pars') <- cons]
--     resTy pars' = arrs (pars ++ pars') (Var (Free c))
--     conFun c' pars' =
--         -- TODO this is wrong, we are putting the body of the parameters and
--         -- not the binders!  Fresh names need to be generated for the arguments
--         -- and then substituted in each type...
--         lams (pars ++ pars') (Constr c' (map snd pars) (map snd pars'))

-- -- | Adds the type constructors and the data declarations as abstracted variable
-- --   to an environment, @'Left' n@ if name @n@ is already present.
-- addData :: Env -> ConId -> DataBody -> Either ConId Env
-- addData env@Env{envData = dds} dd@(Data c₁ _ _ _) =
--     do env₁ <- if Map.member c₁ dds
--                then Left c₁
--                else Right (env{envData = Map.insert c₁ dd dds})
--        let (tyc, cons) = dataDecl dd
--        foldr (\(c₂, (tym, tm)) enve ->
--                do env₂ <- enve;
--                   maybe (Left c₂) Right (addCtx env₂ c₂ tym tm))
--              (Right env₁) (tyc : cons)
