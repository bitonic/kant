-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Tm', due to bound.
module Kant.Env
    ( ConstrRef
    , ConstrsRef
    , Env(..)
    , EnvT
    , EnvP
    , EnvId
    , envType
    , envBody
    , envADT
    , envRec'
    , envRec
    , newEnv
    , addFree
    , addADT
    , addRec
    ) where

import           Control.Monad (join)

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
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
    { envDefs    :: HashMap Id (TmRefId, Maybe TmRefId)
    , envADTs    :: HashMap ConId ADT
    , envRecs    :: HashMap ConId Record
    , envConstrs :: ConstrsRef
    , envCurs    :: Cursor f v
    , envRef     :: Ref
    }
type EnvT = Env TmRef
type EnvP = Env Proxy

instance IsCursor Env where
    getCurs = envCurs
    putCurs c env = env{envCurs = c}

envType :: Eq v => EnvT v -> v -> Maybe (TmRef v)
envType env@Env{envDefs = defs} v =
    case free' env v of
        Just n  -> fmap (nest env) . fst <$> HashMap.lookup n defs
        Nothing -> Just (ctx env v)

envBody :: Eq v => Env f v -> v -> Maybe (TmRef v)
envBody env@Env{envDefs = defs} v =
    do n <- free' env v
       fmap (nest env) <$> join (snd <$> HashMap.lookup n defs)

envADT :: Eq v => Env f v -> ConId -> ADT
envADT Env{envADTs = adts} v =
    case HashMap.lookup v adts of
        Nothing  -> IMPOSSIBLE("looking up non-existant ADT")
        Just adt -> adt

envRec' :: Eq v => Env f v -> ConId -> Maybe Record
envRec' Env{envRecs = recs} v = HashMap.lookup v recs

envRec :: Eq v => Env f v -> ConId -> Record
envRec env v =
    case envRec' env v of
        Nothing  -> IMPOSSIBLE("lookinp up non-existant record")
        Just rec -> rec

type EnvId = EnvT Id

newEnv :: EnvId
newEnv = Env{ envDefs    = HashMap.empty
            , envADTs    = HashMap.empty
            , envRecs    = HashMap.empty
            , envConstrs = Constr.empty
            , envCurs    = newCurs
            , envRef     = 0 }

addFree :: Eq v => EnvT v -> Id -> TmRefId -> Maybe TmRefId -> EnvT v
addFree env@Env{envDefs = defs} v ty mt =
    env{envDefs = HashMap.insert v (ty, mt) defs}

addADT :: EnvT v -> Id -> ADT -> EnvT v
addADT env@Env{envADTs = adts} n adt = env{envADTs = HashMap.insert n adt adts}

addRec :: EnvT v -> Id -> Record -> EnvT v
addRec env@Env{envRecs = recs} n rec = env{envRecs = HashMap.insert n rec recs}
