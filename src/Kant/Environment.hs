{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ViewPatterns #-}
-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Term', due to bound.
module Kant.Environment
    ( ItemT(..)
    , Item
    , CtxT
    , Ctx
    , NestT
    , Nest
    , PullT
    , Pull
    , EnvT
    , envNest
    , envPull
    , envCtx
    , Env
      -- * Utilities
    , nestEnv
    , lookupTy
    , lookupDef
    , newEnv
    , pullTerm
    , addAbst
    , addVal
    , addData
    ) where

import           Control.Applicative ((<$>))
import           Data.Foldable (Foldable)
import           Data.Foldable (foldr)
import           Data.Maybe (fromMaybe)
import           Data.Traversable (Traversable)
import           Prelude hiding (foldr)

import           Data.Map (Map)
import qualified Data.Map as Map

import           Bound
import           Bound.Name

import           Kant.Syntax

-- | The inhabitants of our environment
data ItemT a
    = Constr Constr Term        -- ^ Constructor with its type.
    | TyConstr Term [Constr]    -- ^ Type constructor and associated data
                                --   constructors.
    | DeclVal Term Term         -- ^ Declared value, type and value - the value
                                --   will be the 'Var' itself for postulated
                                --   variables.
    | Abstract (TermT a)        -- ^ Abstracted variable, with its type.
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)
type Item = ItemT Id

-- | Given a bound name, returns the matching 'ItemT', if present.
type CtxT a = (a -> Maybe (ItemT a))
type Ctx = CtxT Id

-- | Nests an 'Id' the required amount of times to turn it into a top level
--   variable.
type NestT a = Id -> a
type Nest = NestT Id

-- | Extracts the name out of the bound variable, and the how nested it is.
type PullT a = a -> Id
type Pull = PullT Id

-- | Bringing it all together
data EnvT a = Env
    { envCtx   :: CtxT a
    , envNest  :: NestT a
    , envPull  :: PullT a
    }
type Env = EnvT Id

-- | To be used when we enter a 'Scope', it adjust the environment functions to
--   work with the new level of boundness.
nestEnv :: EnvT a
        -> (b -> Maybe (TermT a))
        -> EnvT (Var (Name Id b) a)
nestEnv Env{envCtx = ctx, envNest = nest, envPull = pull} f =
    Env { envCtx  = \v -> case v of
                              B (Name _ n) -> fmap (Abstract . fmap F) (f n)
                              F v'         -> (F <$>) <$> ctx v'
        , envNest = F . nest
        , envPull = \v -> case v of
                              B b  -> name b
                              F v' -> pull v'
        }

-- | Looks up the type of a variable.
lookupTy :: EnvT a -> a -> Maybe (TermT a)
lookupTy Env{envCtx = ctx, envNest = nest} v =
    case ctx v of
        Nothing              -> Nothing
        Just (Constr _ ty)   -> nest' ty
        Just (TyConstr ty _) -> nest' ty
        Just (DeclVal ty _)  -> nest' ty
        Just (Abstract ty)   -> Just ty
  where nest' ty = Just (nest <$> ty)

-- | Looks up the body of a definition.
lookupDef :: a -> EnvT a -> Maybe (TermT a)
lookupDef v Env{envCtx = ctx, envNest = nest} =
    case ctx v of
        Nothing            -> Nothing
        Just (DeclVal _ t) -> Just (nest <$> t)
        _                  -> Nothing

-- | Creates a new environment given a lookup function for top level
--   declarations.
newEnv :: (Id -> Maybe Item) -> Env
newEnv ctx = Env{ envCtx   = ctx
                , envNest  = id
                , envPull  = id
                }

-- | Checks if a variable refers to a top level thing
isTop :: Eq a => EnvT a -> a -> Bool
isTop env v = envNest env (envPull env v) == v

-- TODO remove duplicates in bound names
-- | Slams a @'TermT' a@ back to a 'Term', by replacing all the abstracted
--   variables with identifiers.  Distinguishes duplicate names while keeping top
--   level names alone.  It's called 'pullTerm' but it really works with any
--   'Foldable'.
pullTerm :: (Ord a, Functor f, Foldable f) => EnvT a -> f a -> f Id
pullTerm env@Env{envPull = pull} t = (mn' Map.!) <$> t
  where
    format 0 n = n
    format i n = n ++ show i

    -- We first insert all the top level ones, so we know they are going to have
    -- count 0
    collect1 v@(isTop env -> True) (mcount, mn) =
        (Map.insert (pull v) 0 mcount, Map.insert v (pull v) mn)
    collect1 _ ms = ms

    -- Then the rest.
    collect2 v ms@(_, Map.lookup v -> Just _) = ms
    collect2 v (mcount, mn) =
        let n = pull v
            c = fromMaybe 0 (Map.lookup n mcount)
        in (Map.insert (pull v) c mcount, Map.insert v (format c n) mn)

    (_, mn') = foldr collect2
                     (foldr collect1 (Map.empty :: Map Id Int, Map.empty) t) t

addCtx :: Eq a => EnvT a -> a -> ItemT a -> Maybe (EnvT a)
addCtx env@Env{envCtx = ctx} v₁ it =
    case ctx v₁ of
        Nothing -> Just (env{envCtx = \v₂ -> if v₁ == v₂ then Just it else ctx v₂})
        Just _  -> Nothing

-- | Adds an abstracted variable to an environment, 'Nothing' if the name is
--   already present.
addAbst :: Eq a => EnvT a -> a -> TermT a -> Maybe (EnvT a)
addAbst env v₁ t = addCtx env v₁ (Abstract t)

-- | Adds a value definition to an environment, 'Nothing' if the name is already
--   present.
addVal :: Env -> Val -> Maybe Env
addVal env (Val n ty t) = addCtx env n (DeclVal ty t)

-- | Adds the type constructors and the data declarations as abstracted variable
--   to an environment, @'Left' n@ if name @n@ is already present.
addData :: Env -> Data -> Either Id Env
addData env dat =
    let (tyc, cons) = dataDecl dat
    in foldr (\(c, ty) enve ->
               do env' <- enve;
                  maybe (Left c) Right (addCtx env' c (Abstract ty)))
             (Right env) (tyc : cons)
