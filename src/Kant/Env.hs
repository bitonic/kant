-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Term', due to bound.
module Kant.Env
    ( ConstrRef
    , ConstrsRef
    , Env(..)
    , EnvId
    , newEnv
    , nestEnv
    , nestEnvTy
    , envFree
    , addFree
    , envFreeVs
    , addADT
    ) where

import           Data.Foldable (foldMap)

import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet

import           Bound
import           Bound.Name

import           Data.Constraint (Constr, Constrs)
import qualified Data.Constraint as Constr
import           Kant.Common
import           Kant.Term
import           Kant.ADT
#include "../impossible.h"

type Value = TermRef
type Ctx v = v -> Maybe (Value v)
type ConstrRef = Constr Ref
type ConstrsRef = Constrs Ref

-- | Bringing it all together
data Env v = Env
    { envValue   :: Ctx v
    , envType    :: Ctx v
    , envADTs    :: ConId -> ADT
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
            , envADTs    = IMPOSSIBLE("looking up a non-existant adt")
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

addADT :: Env v -> Id -> ADT -> Env v
addADT env@Env{envADTs = adts} n adt =
    env{envADTs = \n' -> if n == n' then adt else adts n'}
