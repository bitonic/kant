{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ViewPatterns #-}
-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Term', due to bound.
module Kant.Environment
    ( CtxT
    , Ctx
    , NestT
    , Nest
    , PullT
    , Pull
    , EnvT(..)
    , Env
      -- * Utilities
    , nestEnv
    , nestEnv'
    , envTy
    , envDef
    , envData'
    , newEnv
    , pullTerm
    , addAbst
    , addVal
    , dataDecl
    , addData
    , caseRefine
    ) where

import           Control.Applicative ((<$>))
import           Control.Arrow (second)
import           Control.Monad (join)
import           Data.Foldable (Foldable)
import           Data.Foldable (foldr)
import           Data.Maybe (fromMaybe)
import           Prelude hiding (foldr)

import           Data.Map (Map)
import qualified Data.Map as Map

import           Bound
import           Bound.Name

import           Kant.Term

type ItemT a = (TermT a, Maybe (TermT a))
type Item = ItemT Id

type CtxT a = (a -> Maybe (ItemT a))
type Ctx = CtxT Id

type CtxData = Map Id Data

-- | Nests an 'Id' the required amount of times to turn it into a top level
--   variable.
type NestT a = Id -> a
type Nest = NestT Id

-- | Extracts the name out of the bound variable.
type PullT a = a -> Id
type Pull = PullT Id

-- | Bringing it all together
data EnvT a = Env
    { envCtx  :: CtxT a
    , envData :: CtxData
    , envNest :: NestT a
    , envPull :: PullT a
    }
type Env = EnvT Id

-- | To be used when we enter a 'Scope', it adjust the environment functions to
--   work with the new level of boundness.
nestEnv :: EnvT a
        -> (b -> Maybe (TermT (Var (Name Id b) a)))
        -> EnvT (Var (Name Id b) a)
nestEnv env@Env{envCtx = ctx, envNest = nest, envPull = pull} f =
    env{ envCtx =
         \v -> case v of
                  B (Name _ n) -> (\t      -> (t,       Nothing))       <$> f n
                  F v'         -> (\(t, m) -> (F <$> t, (F <$>) <$> m)) <$> ctx v'
       , envNest = F . nest
       , envPull = \v -> case v of
                             B b  -> name b
                             F v' -> pull v'
       }

-- | Like 'nestEnv' but accepts a function that returns terms of the outer
-- scope, and automatically nests them.
nestEnv' :: EnvT a -> (b -> Maybe (TermT a)) -> EnvT (Var (Name Id b) a)
nestEnv' env f = nestEnv env (\n -> (F <$>) <$> f n)

-- | Looks up the type of a variable.
envTy :: EnvT a -> a -> Maybe (TermT a)
envTy Env{envCtx = ctx} v = fst <$> ctx v

-- | Looks up the body of a definition.
envDef :: EnvT a -> a -> Maybe (TermT a)
envDef Env{envCtx = ctx} v = join (snd <$> ctx v)

envData' :: Eq a => EnvT a -> a -> Maybe Data
envData' env@Env{envData = dat, envPull = pull} v =
    if isTop env v then Map.lookup (pull v) dat else Nothing

newEnv :: Env
newEnv = Env{ envCtx  = const Nothing
            , envData = Map.empty
            , envNest = id
            , envPull = id
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
addAbst env v₁ t = addCtx env v₁ (t, Nothing)

-- | Adds a value definition to an environment, 'Nothing' if the name is already
--   present.
addVal :: Env -> Id -> Term -> Term -> Maybe Env
addVal env n ty t = addCtx env n (ty, (Just t))

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
    ((c, (params pi_ pars (Type l), Nothing)),
     [ let pars' = map (second (instantiateList args)) s
       in (c', (params pi_ (pars ++ pars') resTy, Just (conFun c' pars')))
     | ConstrT c' s <- cons ])
  where
    args = map (Var . fst) pars
    resTy = app (Var c : args)
    conFun c' pars' = lams (pars ++ pars')
                           (Constr c' (map (Var . fst) pars) (map (Var . fst) pars'))

-- | Adds the type constructors and the data declarations as abstracted variable
--   to an environment, @'Left' n@ if name @n@ is already present.
addData :: Env -> Data -> Either Id Env
addData env@Env{envData = dat} dd@(Data c₁ _ _ _) =
    do env' <- if Map.member c₁ dat
               then Left c₁
               else Right (env{envData = Map.insert c₁ dd dat})
       let (tyc, cons) = dataDecl dd
       foldr (\(c₂, item) enve ->
               do env'' <- enve;
                  maybe (Left c₂) Right (addCtx env'' c₂ item))
             (Right env') (tyc : cons)

caseRefine :: Eq a => EnvT a -> a -> TermT a -> TermT a -> EnvT a
caseRefine env@Env{envCtx = ctx} v₁ ty t =
    env{envCtx = \v₂ -> if v₁ == v₂ then Just (ty, Just t) else ctx v₂}
