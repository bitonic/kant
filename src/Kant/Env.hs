-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Term', due to bound.
module Kant.Env
    ( ConstrRef
    , ConstrsRef
    , Env(..)
    , EnvT
    , EnvP
    , EnvId
    , envPull
    , envNest
    , envType
    , envBody
    , envADT
    , newEnv
    , nestEnv
    , envFree
    , addFree
    , envFreeVs
    , addADT
    , toEnvP
    ) where

import           Control.Monad (join)
import           Data.Foldable (foldMap)

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet

import           Bound
import           Bound.Name
import           Data.Proxy

import           Data.Constraint (Constr, Constrs)
import qualified Data.Constraint as Constr
import           Kant.ADT
import           Kant.Common
import           Kant.Cursor
import           Kant.Term
#include "../impossible.h"

type ConstrRef = Constr Ref
type ConstrsRef = Constrs Ref

-- | Bringing it all together
data Env f v = Env
    { envDefs    :: HashMap Id (TermRefId, Maybe TermRefId)
    , envADTs    :: HashMap ConId ADT
    , envConstrs :: ConstrsRef
    , envCurs    :: Cursor f v
    , envRef     :: Ref
    }
type EnvT = Env TermRef
type EnvP = Env Proxy

envPull :: Env f v -> v -> Id
envPull = cursPull . envCurs

envNest :: Env f v -> Id -> v
envNest = cursNest . envCurs

envType :: Eq v => EnvT v -> v -> Maybe (TermRef v)
envType env@Env{envDefs = defs, envCurs = curs} v =
    if envFree env v
    then fmap (envNest env) . fst <$> HashMap.lookup (envPull env v) defs
    else Just (cursCtx curs v)

envBody :: Eq v => Env f v -> v -> Maybe (TermRef v)
envBody env@Env{envDefs = defs} v =
    if envFree env v
    then fmap (envNest env) <$> join (snd <$> HashMap.lookup (envPull env v) defs)
    else Nothing

envADT :: Eq v => Env f v -> ConId -> ADT
envADT Env{envADTs = adts} v =
    case HashMap.lookup v adts of
        Nothing  -> IMPOSSIBLE("looking up non-existant ADT")
        Just adt -> adt

type EnvId = EnvT Id

nestEnv :: Functor f => Env f v -> f v -> Env f (Var (Name Id ()) v)
nestEnv env@Env{envCurs = curs} ty = env{envCurs = nestCurs curs ty}

newEnv :: EnvId
newEnv = Env{ envDefs    = HashMap.empty
            , envADTs    = HashMap.empty
            , envConstrs = Constr.empty
            , envCurs    = newCurs
            , envRef     = 0 }

envFree :: Eq v => Env f v -> v -> Bool
envFree Env{envCurs = curs} v = cursFree curs v

addFree :: Eq v => EnvT v -> Id -> TermRefId -> Maybe TermRefId -> EnvT v
addFree env@Env{envDefs = defs} v ty mt =
    env{envDefs = HashMap.insert v (ty, mt) defs}

envFreeVs :: VarC v => Env f v -> TermRef v -> HashSet Id
envFreeVs env = foldMap (\v -> if envFree env v
                               then HashSet.singleton (envPull env v)
                               else HashSet.empty)

addADT :: EnvT v -> Id -> ADT -> EnvT v
addADT env@Env{envADTs = adts} n adt = env{envADTs = HashMap.insert n adt adts}

toEnvP :: Env f v -> EnvP v
toEnvP Env{ envDefs = defs
          , envADTs = adts
          , envConstrs = constrs
          , envCurs    = curs
          , envRef     = ref
          } = Env{ envDefs    = defs
                 , envADTs    = adts
                 , envConstrs = constrs
                 , envCurs    = toCursP curs
                 , envRef     = ref
                 }
