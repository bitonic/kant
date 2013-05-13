-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Tm', due to bound.
module Kant.Env
    ( ConstrRef
    , ConstrsRef
    , Env(..)
    , EnvT
    , EnvP
    , EnvId
    , envVar
    , envBody
    , envADT
    , envRec
    , isRec
    , newEnv
    , addFree
    , addADT
    , addRec
    , envDup
    ) where

import           Control.Monad (join)
import           Data.Maybe (isJust)

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
type EnvT = Env Param
type EnvP = Env Proxy

instance IsCursor Env where
    getCurs = envCurs
    putCurs c env = env{envCurs = c}

envVar :: Eq v => EnvT v -> v -> Twin -> Maybe (TmRef v)
envVar env@Env{envDefs = defs} v w =
    case free' env v of
        Just n  -> fmap (nest env) . fst <$> HashMap.lookup n defs
        Nothing -> case (ctx env v, w) of
                       (P ty,        Only ) -> Just ty
                       (Twins ty _ , TwinL) -> Just ty
                       (Twins _  ty, TwinR) -> Just ty
                       -- TODO maybe dedicated error or crash in this case?
                       _                    -> Nothing

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

isRec :: Eq v => Env f v -> v -> Bool
isRec env v = free env v && isJust (envRec' env (pull env v))

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

envDup :: Env f v -> Id -> Bool
envDup Env{envDefs = defs} n = HashMap.member n defs
