-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Term', due to bound.
module Kant.Env
    ( Env(..)
    , EnvId
    , newEnv
    , nestEnv
    , nestEnvTy
    , envFree
    , addFree
    ) where

import           Control.Applicative ((<$>))

import           Bound
import           Bound.Name

import           Kant.Term

type Ctx v = v -> Maybe (Term v)

-- | Bringing it all together
data Env v = Env
    { envValue  :: Ctx v
    , envType   :: Ctx v
    , envPull   :: v -> Id
    , envNest   :: Id -> v
    , envRename :: v -> (Id -> Id) -> v
    }

type EnvId = Env Id

nestf :: Maybe (Term v) -> Ctx v -> Ctx (Var (NameId ()) v)
nestf t _ (B _) = fmap F <$> t
nestf _ f (F v) = fmap F <$> f v

nestEnv :: Env v -> Maybe (Term v) -> Maybe (Term v) -> Env (Var (Name Id ()) v)
nestEnv Env{ envValue = value
           , envType = type_
           , envPull = pull
           , envNest = nest
           , envRename = rename
           } t ty =
    Env{ envValue  = nestf t value
       , envType   = nestf ty type_
       , envPull   = \v -> case v of B n -> name n; F v' -> pull v'
       , envNest   = F . nest
       , envRename = \v f -> case v of B (Name n ()) -> B (Name (f n) ())
                                       F v'          -> F (rename v' f)
       }

newEnv :: EnvId
newEnv = Env{ envValue  = const Nothing
            , envType   = const Nothing
            , envPull   = id
            , envNest   = id
            , envRename = \v f -> f v
            }

nestEnvTy :: Env v -> Term v -> Env (Var (NameId ()) v)
nestEnvTy env ty = nestEnv env Nothing (Just ty)

envFree :: Eq v => Env v -> v -> Bool
envFree Env{envPull = pull, envNest = nest} v = v == nest (pull v)

addFree :: Eq v => Env v -> v -> Maybe (Term v) -> Maybe (Term v) -> Env v
addFree env@Env{envValue = value, envType = type_} v mv mty =
    env{ envValue = \v' -> if v == v' then mv  else value v'
       , envType  = \v' -> if v == v' then mty else type_ v'
       }