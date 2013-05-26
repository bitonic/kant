-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Tm', due to bound.
module Kant.Env
    ( ConstrRef
    , ConstrsRef
    , Free(..)
    , Env(..)
    , EnvT
    , EnvP
    , EnvId
    , envType
    , envBody
    , envADT
    , envRec
    , isRec
    , newEnv
    , addFree
    , addADT
    , addRec
    ) where

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
    { envFrees   :: HashMap Id Free
    , envADTs    :: HashMap ConId ADT
    , envRecs    :: HashMap ConId Rec
    , envConstrs :: ConstrsRef
    , envCurs    :: Cursor f v
    , envRef     :: Ref
    }
type EnvT = Env TmRef
type EnvP = Env Proxy

data Free
    = Abstract TmRefId
    | Value TmRefId TmRefId
    | DataCon ConId
    | DataElim ConId
    | RecProj ConId

defType :: Free -> Maybe TmRefId
defType (Abstract ty) = Just ty
defType (Value ty _)  = Just ty
defType _             = Nothing

instance IsCursor Env where
    getCurs = envCurs
    putCurs c env = env{envCurs = c}

envType :: Eq v => EnvT v -> v -> Maybe (TmRef v)
envType env@Env{envFrees = defs} v =
    case free' env v of
        Just n  -> fmap (nest env) <$> (defType =<< HashMap.lookup n defs)
        Nothing -> Just (ctx env v)

envBody :: Eq v => Env f v -> v -> Maybe (TmRef v)
envBody env@Env{envFrees = defs} v =
    do n <- free' env v
       fmap (nest env) <$> (defType =<< HashMap.lookup n defs)

envADT :: Eq v => Env f v -> ConId -> ADT
envADT Env{envADTs = adts} v =
    case HashMap.lookup v adts of
        Nothing  -> IMPOSSIBLE("looking up non-existant ADT")
        Just adt -> adt

envRec' :: Eq v => Env f v -> ConId -> Maybe Rec
envRec' Env{envRecs = recs} v = HashMap.lookup v recs

envRec :: Eq v => Env f v -> ConId -> Rec
envRec env v =
    case envRec' env v of
        Nothing  -> IMPOSSIBLE("looking up non-existant record")
        Just rec -> rec

isRec :: Eq v => Env f v -> v -> Bool
isRec env v = free env v && isJust (envRec' env (pull env v))

type EnvId = EnvT Id

newEnv :: EnvId
newEnv = Env{ envFrees    = HashMap.empty
            , envADTs    = HashMap.empty
            , envRecs    = HashMap.empty
            , envConstrs = Constr.empty
            , envCurs    = newCurs
            , envRef     = 0 }

addFree :: Eq v => EnvT v -> Id -> Free -> EnvT v
addFree env@Env{envFrees = defs} v def =
    env{envFrees = HashMap.insert v def defs}

addADT :: EnvT v -> Id -> ADT -> EnvT v
addADT env@Env{envADTs = adts} n adt = env{envADTs = HashMap.insert n adt adts}

addRec :: EnvT v -> Id -> Rec -> EnvT v
addRec env@Env{envRecs = recs} n rec = env{envRecs = HashMap.insert n rec recs}
