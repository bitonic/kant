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
      -- * Utilities
    , toTag
    , bumpCount
    , envTy
    , envDef
    , envData'
    , newEnv
    , addAbst
    , addVal
    , addData
    , upAbst
    , upAbst'
    , upVal
    , upVal'
    ) where

import           Control.Applicative ((<$>))
import           Control.Monad (join)
import           Data.Foldable (foldr)
import           Prelude hiding (foldr)

import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as Text

import           Kant.Name
import           Kant.Term

type Item = (Maybe Term, Maybe Term)

type Count = Integer

-- | Bringing it all together
data Env = Env
    { envCtx   :: Map TName Item
    , envData  :: Map ConId Data
    , envCount :: Count
    }

bumpCount :: Env -> (Count, Env)
bumpCount env@Env{envCount = c} = (c, env{envCount = c+1})

toTag :: Count -> Tag
toTag = Text.pack . show

-- | Looks up the type of a variable.
envTy :: Env -> TName -> Maybe Term
envTy Env{envCtx = ctx} v = join (fst <$> Map.lookup v ctx)

-- | Looks up the body of a definition.
envDef :: Env -> TName -> Maybe Term
envDef Env{envCtx = ctx} v = join (snd <$> Map.lookup v ctx)

envData' :: Env -> TName -> Maybe Data
envData' Env{envData = dds} (Free n) = Map.lookup n dds
envData' _                  _        = Nothing

newEnv :: Env
newEnv = Env{ envCtx   = Map.empty
            , envData  = Map.empty
            , envCount = 0
            }

addCtx :: Env -> Id -> Maybe Term -> Maybe Term -> Maybe Env
addCtx env@Env{envCtx = ctx} n tym tm =
    case Map.lookup (Free n) ctx of
        Nothing -> Just (env{envCtx = Map.insert (Free n) (tym, tm) ctx})
        Just _  -> Nothing

-- | Adds an abstracted variable to an environment, 'Nothing' if the name is
--   already present.
addAbst :: Env -> Id -> Term -> Maybe Env
addAbst env n t = addCtx env n (Just t) Nothing

-- | Adds a value definition to an environment, 'Nothing' if the name is already
--   present.
addVal :: Env -> Id -> Term -> Term -> Maybe Env
addVal env v ty t = addCtx env v (Just ty) (Just t)

upCtx :: Env -> TName -> Maybe Term -> Maybe Term -> Env
upCtx env@Env{envCtx = ctx} v tym tm = env{envCtx = Map.insert v (tym, tm) ctx}

upAbst :: Env -> TName -> Term -> Env
upAbst env v t = upCtx env v (Just t) Nothing

upAbst' :: Env -> TBinder -> Term -> Env
upAbst' env Wild        _ = env
upAbst' env (Bind _ ta) t = upAbst env (Bound ta) t

upVal :: Env -> TName -> Term -> Term -> Env
upVal env v ty t = upCtx env v (Just ty) (Just t)

upVal' :: Env -> TBinder -> Term -> Term -> Env
upVal' env (Bind _ ta) ty t = upVal env (Bound ta) ty t
upVal' env Wild        _  _ = env

-- | Extracts the types out of a data declaration.
--
--   A type function will be generated as type constructor, taking the
--   parameters as arguments and returning someting of @Type l@, where @l@ is
--   the level specified in the declaration.
--
--   Another function will be generated for each data constructor, taking all
--   the parameters of the type constructor plus its own parameter.
dataDecl :: Data -> ((Id, Item), [(Id, Item)])
dataDecl (Data c pars l cons) =
    ((c, (Just (arrs pars (Type l)), Nothing)), cons')
  where
    cons' = [(c', (Just (resTy pars'), Just (conFun c' pars'))) | (c', pars') <- cons]
    resTy pars' = arrs (pars ++ pars') (Var (Free c))
    conFun c' pars' =
        lams (pars ++ pars') (Constr c' (map snd pars) (map snd pars'))

-- | Adds the type constructors and the data declarations as abstracted variable
--   to an environment, @'Left' n@ if name @n@ is already present.
addData :: Env -> Data -> Either ConId Env
addData env@Env{envData = dds} dd@(Data c₁ _ _ _) =
    do env₁ <- if Map.member c₁ dds
               then Left c₁
               else Right (env{envData = Map.insert c₁ dd dds})
       let (tyc, cons) = dataDecl dd
       foldr (\(c₂, (tym, tm)) enve ->
               do env₂ <- enve;
                  maybe (Left c₂) Right (addCtx env₂ c₂ tym tm))
             (Right env₁) (tyc : cons)
