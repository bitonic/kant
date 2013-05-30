-- | Sets up a warm place (cit) to look up definitions, both top level and
--   bound, using a 'Cursor'.  Also, stores the set of constraints for the
--   type hierarchy.
module Kant.Env
    ( Free(..)
    , ConstrRef
    , ConstrsRef
    , Env(..)
    , EnvT
    , EnvP
    , EnvId
    , envFree
    , envType
    , envBody
    , envADT
    , envRec
    , newEnv
    , addFree
    , addADT
    , addRec
    ) where

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

-- | Free names will refer to one of these.
data Free
    = Abstract TmRefId          -- ^ @postulate@ variable.
    | Value TmRefId TmRefId     -- ^ Declared value.
    | DataCon ConId             -- ^ Datacon for certain ADT (the 'ConId').
    | DataElim ConId            -- ^ Eliminator for certain ADT
    | RecCon ConId              -- ^ Datacon for certain record.
    | RecProj ConId             -- ^ Projection for certain record.

type ConstrRef = Constr Ref
type ConstrsRef = Constrs Ref

data Env f v = Env
    { envFrees   :: HashMap Id Free
      -- ^ Free names.
    , envADTs    :: HashMap ConId ADT
      -- ^ ADTs, indexed by their tycon name.
    , envRecs    :: HashMap ConId Rec
      -- ^ Records, indexed by their tycon name.
    , envConstrs :: ConstrsRef
      -- ^ Set of constraints for the type hierarchy.
    , envCurs    :: Cursor f v
      -- ^ Cursor to navigate 'Tm's.
    , envRef     :: Ref
      -- ^ A counter to generate fresh 'Ref's.
    }
type EnvT = Env TmRef
type EnvP = Env Proxy

-- | Gets the type of a 'Free', if it refers to a postulated of defined
--   variable.
freeType :: Free -> Maybe TmRefId
freeType (Abstract ty) = Just ty
freeType (Value ty _)  = Just ty
freeType _             = Nothing

-- | Gets the body of a 'Free', if it refers to a defined variable.
freeBody :: Free -> Maybe TmRefId
freeBody (Value _ t) = Just t
freeBody _           = Nothing

instance IsCursor Env where
    getCurs = envCurs
    putCurs c env = env{envCurs = c}

-- | Gets a 'Free' given an 'Id', if present.
envFree :: Env f v -> Id -> Maybe Free
envFree Env{envFrees = frees} n = HashMap.lookup n frees

-- | Gets the type given an 'Id', if the 'Id' refers to a postulated of
--   defined variable.
envType :: Eq v => EnvT v -> v -> Maybe (TmRef v)
envType env v =
    case free' env v of
        Just n  -> fmap (nest env) <$> (freeType =<< envFree env n)
        Nothing -> Just (ctx env v)

-- | Gets the body given an 'Id', if the 'Id' refers to a defined variable.
envBody :: Eq v => Env f v -> v -> Maybe (TmRef v)
envBody env v =
    do n <- free' env v
       fmap (nest env) <$> (freeBody =<< envFree env n)

-- | Gets an 'ADT' given a 'ConId', panics if it's not present.
envADT :: Env f v -> ConId -> ADT
envADT Env{envADTs = adts} v =
    case HashMap.lookup v adts of
        Nothing  -> IMPOSSIBLE("looking up non-existant ADT")
        Just adt -> adt

-- | Gets a 'Rec' given a 'ConId', panics if it's not present.
envRec :: Env f v -> ConId -> Rec
envRec Env{envRecs = recs} v =
    case HashMap.lookup v recs of
        Nothing  -> IMPOSSIBLE("looking up non-existant record")
        Just rec -> rec

type EnvId = EnvT Id

newEnv :: EnvId
newEnv = Env{ envFrees    = HashMap.empty
            , envADTs    = HashMap.empty
            , envRecs    = HashMap.empty
            , envConstrs = Constr.empty
            , envCurs    = newCurs
            , envRef     = 0
            }

addFree :: Eq v => EnvT v -> Id -> Free -> EnvT v
addFree env@Env{envFrees = defs} v def =
    env{envFrees = HashMap.insert v def defs}

addADT :: EnvT v -> Id -> ADT -> EnvT v
addADT env@Env{envADTs = adts} n adt = env{envADTs = HashMap.insert n adt adts}

addRec :: EnvT v -> Id -> Rec -> EnvT v
addRec env@Env{envRecs = recs} n rec = env{envRecs = HashMap.insert n rec recs}
