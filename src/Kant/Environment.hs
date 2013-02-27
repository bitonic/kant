{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Term', due to bound.
module Kant.Environment
    ( Env(..)
      -- * Utilities
    , envTy
    , envDef
    , envData'
    , newEnv
    , addAbst
    , addVal
    , upAbst
    , upVal
    , addData
    ) where

import           Control.Applicative ((<$>))
import           Control.Monad (join)
import           Data.Foldable (foldrM)
import           Data.List (inits)

import           Control.Monad.Error (MonadError(..))
import           Data.Map (Map)
import qualified Data.Map as Map

import           Kant.Name
import           Kant.Term

type Item = (Maybe Term, Maybe Term)

-- | Bringing it all together
data Env = Env
    { envCtx   :: Map TName Item
    , envData  :: Map ConId DataBody
    }

-- | Looks up the type of a variable.
envTy :: Env -> TName -> Maybe Term
envTy Env{envCtx = ctx} v = join (fst <$> Map.lookup v ctx)

-- | Looks up the body of a definition.
envDef :: Env -> TName -> Maybe Term
envDef Env{envCtx = ctx} v = join (snd <$> Map.lookup v ctx)

envData' :: Env -> ConId -> Maybe DataBody
envData' Env{envData = dds} v = Map.lookup v dds

newEnv :: Env
newEnv = Env{ envCtx   = Map.empty
            , envData  = Map.empty
            }

addCtx :: Env -> TName -> Maybe Term -> Maybe Term -> Maybe Env
addCtx env@Env{envCtx = ctx} v tym tm =
    case Map.lookup v ctx of
        Nothing -> Just env{envCtx = Map.insert v (tym, tm) ctx}
        Just _  -> Nothing

-- | Adds an abstracted variable to an environment, 'Nothing' if the name is
--   already present.
addAbst :: Env -> TName -> Term -> Maybe Env
addAbst env n t = addCtx env n (Just t) Nothing

-- | Adds a value definition to an environment, 'Nothing' if the name is already
--   present.
addVal :: Env -> TName -> Term -> Term -> Maybe Env
addVal env v ty t = addCtx env v (Just ty) (Just t)

upCtx :: Env -> TName -> Maybe Term -> Maybe Term -> Env
upCtx env@Env{envCtx = ctx} v tym tm = env{envCtx = Map.insert v (tym, tm) ctx}

upAbst :: Env -> TName -> Term -> Env
upAbst env v t = upCtx env v (Just t) Nothing

upVal :: Env -> TName -> Term -> Term -> Env
upVal env v ty t = upCtx env v (Just ty) (Just t)

-- | Adds the type constructors and the data declarations as abstracted variable
--   to an environment, @'Left' n@ if name @n@ is already present.
addData :: (MonadSubst m, MonadError e m)
        => Env -> ConId -> DataBody -> (ConId -> e) -> m Env
addData env₁@Env{envData = dds} tyc dd@(Tele typars₁ (DataT l cons)) err =
    -- TODO here we manipulate things and build up terms, but do we avoid name
    -- capturing?  I think it's better to refresh all variables.
    do checkDup tyc env₁
       let env₂       = env₁{envData = Map.insert tyc dd dds}
           Just env₃ = addAbst env₂ (free tyc) (pis typars₁ (Type l))
       typars₂ <- mapM freshV typars₁
       let tybs = zip (map fst typars₁) (getV typars₂)
       typars₃ <- sequence [ (b,) <$> substMany bs ty
                           | ((b, ty), bs) <- zip typars₂ (inits tybs) ]
       foldrM (\(ConstrT dc (Tele dpars₁ Proxy)) env₄ ->
                do checkDup dc env₄
                   dpars₂ <- mapM freshV dpars₁
                   dpars₃ <- sequence [ (b,) <$> substMany tybs ty
                                         | (b, ty) <- dpars₂ ]
                   let resTy = app (Var (free tyc) : getV typars₃)
                       f     = conFun dc typars₃ dpars₂
                   let Just env₅ = addVal env₄ (free dc)
                                          (pis (typars₃ ++ dpars₃) resTy) f
                   return env₅) env₃ cons
  where
    checkDup c Env{envCtx = ctx, envData = dds'} =
        if Map.member c dds' || Map.member (free c) ctx
        then throwError (err c)
        else return ()
    getV = map (Var . fst)
    conFun dc typars dpars =
        lams (typars ++ dpars) (Constr dc (getV typars) (getV dpars))
    freshV (v, ty) = (,ty) <$> fresh v
