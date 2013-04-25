{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Term', due to bound.
module Kant.Env
    ( Elim
    , ConstrRef
    , ConstrsRef
    , Env(..)
    , EnvId
    , newEnv
    , nestEnv
    , nestEnvTy
    , envFree
    , addFree
    , envFreeVs
    , addElim
    ) where

import           Data.Foldable (foldMap)

import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet

import           Bound
import           Bound.Name

import           Kant.Common
import           Kant.Term
import           Kant.Constraint (Constr, Constrs)
import qualified Kant.Constraint as Constr
#include "impossible.h"

type Value = TermRef
type Ctx v = v -> Maybe (Value v)
type Elim = forall v. VarC v => [TermRef v] -> Maybe (TermRef v)
type ConstrRef = Constr Ref
type ConstrsRef = Constrs Ref

-- | Bringing it all together
data Env v = Env
    { envValue   :: Ctx v
    , envType    :: Ctx v
    , envElim    :: ConId -> Elim
    , envPull    :: v -> Id
    , envNest    :: Id -> v
    , envRename  :: v -> (Id -> Id) -> v
    , envRef     :: Ref
    , envConstrs :: ConstrsRef
    }

type EnvId = Env Id

nestf :: Maybe (TermRef v) -> Ctx v -> Ctx (Var (NameId ()) v)
nestf t _ (B _) = fmap F <$> t
nestf _ f (F v) = fmap F <$> f v

nestEnv :: Env v -> Maybe (Value v) -> Maybe (Value v)
        -> Env (Var (Name Id ()) v)
nestEnv env@Env{ envValue = value
               , envType   = type_
               , envPull   = pull
               , envNest   = nest
               , envRename = rename
               } t ty =
    env{ envValue  = nestf t value
       , envType   = nestf ty type_
       , envPull   = \v -> case v of B n -> name n; F v' -> pull v'
       , envNest   = F . nest
       , envRename = \v f -> case v of B (Name n ()) -> B (Name (f n) ())
                                       F v'          -> F (rename v' f)
       }

newEnv :: EnvId
newEnv = Env{ envValue   = const Nothing
            , envType    = const Nothing
            , envElim    = IMPOSSIBLE("looking up a non-existant elim")
            , envPull    = id
            , envNest    = id
            , envRename  = \v f -> f v
            , envRef     = 0
            , envConstrs = Constr.empty
            }

nestEnvTy :: Env v -> TermRef v -> Env (Var (NameId ()) v)
nestEnvTy env ty = nestEnv env Nothing (Just ty)

envFree :: Eq v => Env v -> v -> Bool
envFree Env{envPull = pull, envNest = nest} v = v == nest (pull v)

addFree :: Eq v => Env v -> v -> Maybe (TermRef v) -> Maybe (TermRef v) -> Env v
addFree env@Env{envValue = value, envType = type_} v mv mty =
    env{ envValue = \v' -> if v == v' then mv  else value v'
       , envType  = \v' -> if v == v' then mty else type_ v'
       }

envFreeVs :: VarC v => Env v -> TermRef v -> HashSet Id
envFreeVs env = foldMap (\v -> if envFree env v
                               then HashSet.singleton (envPull env v)
                               else HashSet.empty)

addElim :: Env v -> Id -> Elim -> Env v
addElim env@Env{envElim = elim} n el =
    env{envElim = \n' -> if n == n' then el else elim n'}
