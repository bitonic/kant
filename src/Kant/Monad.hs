{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Kant.Monad
    ( -- * Kant 'Monad'
      KMonadT
    , KMonadP
    , KMonadE
    , KMonad(KMonad)
    , runKMonad
    , mapKMonad
    , fromKMonadP
    , throwKError
      -- * Environment actions
    , getEnv
    , putEnv
    , restoreEnv
    , nestM
    , nestPM
    , lookupTy
    , lookupTyCon
    , lookupDataCon
    , lookupElim
    , lookupProj
    , isRecM
    , addFreeM
    , addADTM
    , addRecM
      -- * References
    , freshRef
      -- * Constraints
    , addConstrs
    , addConstrs'
    , addConstr'
      -- * Normal forms
    , whnfM
    , nfM
      -- * Slamming terms
    , slamM
    , formHoleM
      -- * Errors
    , mismatch
    , expectingType
    , expectingFunction
    , expectingTypeData
    , wrongRecTypePos
    , untypedTm
    , unexpectedHole
    , cyclicTypes
    , expectingTypeCon
    , duplicateName
      -- * Parsing
    , processModuleM
    , processDeclM
    , processTmM
    ) where

import           Data.Maybe (fromMaybe)

import qualified Data.Constraint as Constr
import           Kant.ADT
import           Kant.Common
import           Kant.Cursor
import           Kant.Decl
import           Kant.Env
import           Kant.Error
import           Kant.Monad.Base
import           Kant.Parser
import           Kant.Reduce
import           Kant.Ref
import           Kant.Term
import           Kant.Uniquify
#include "../impossible.h"

lookupTy :: (VarC v, Monad m) => v -> KMonadT v m (TmRef v)
lookupTy v =
    do env <- getEnv
       case envType env v of
           Nothing -> throwKError (OutOfBounds (pull env v))
           Just ty -> return ty

doADTRec :: (VarC v, Monad m)
         => ADTRec -> ConId -> (ADT -> a) -> (Rec -> a) -> KMonadE f v m a
doADTRec ADT_ tyc f _ = (f . (`envADT` tyc)) <$> getEnv
doADTRec Rec_  tyc _ f = (f . (`envRec` tyc)) <$> getEnv

lookupTyCon :: (VarC v, Monad m) => ADTRec -> ConId -> KMonadE f v m (TmRef v)
lookupTyCon dt tyc =
    do env <- getEnv
       fmap (nest env) <$> doADTRec dt tyc adtTy recTy

lookupDataCon :: (VarC v, Monad m)
              => ADTRec -> ConId -> ConId -> KMonadE f v m (TmRef v)
lookupDataCon dt tyc dc =
    do env <- getEnv
       let err = IMPOSSIBLE("Constructor " ++ dc ++ " for " ++ tyc ++ " not present")
       dcty <- doADTRec dt tyc
                        (\adt -> fromMaybe err (lookup dc (adtCons adt)))
                        (\rec -> case recCon rec of
                                     (dc', ty) | dc == dc' -> ty
                                     _ -> err)
       return (nest env <$> dcty)

lookupElim :: (VarC v, Monad m) => ConId -> KMonadE f v m (TmRef v)
lookupElim tyc =
    do env <- getEnv
       return (nest env <$> adtElim (envADT env tyc))

lookupProj :: (VarC v, Monad m) => ConId -> Id -> KMonadE f v m (TmRef v)
lookupProj tyc pr =
    do env <- getEnv
       return $ case lookup pr (recProjs (envRec env tyc)) of
                    Nothing -> IMPOSSIBLE("Projection not present")
                    Just ty -> nest env <$> ty

isRecM :: (VarC v, Monad m) => v -> KMonadT v m Bool
isRecM v = do env <- getEnv; return (isRec env v)

addFreeM :: (VarC v, Monad m) => Id -> Free -> KMonadT v m ()
addFreeM v def = do env <- getEnv; putEnv (addFree env v def)

addADTM :: (Monad m) => ConId -> ADT -> KMonadT v m ()
addADTM n adt = do env <- getEnv; putEnv (addADT env n adt)

addRecM :: (Monad m) => ConId -> Rec -> KMonadT v m ()
addRecM n rec = do env <- getEnv; putEnv (addRec env n rec)

addConstrs :: (Monad m) => [ConstrRef] -> KMonadE f v m ()
addConstrs cs =
    do env <- getEnv
       constrs <- maybe cyclicTypes return (Constr.addConstrs cs (envConstrs env))
       putEnv (env{envConstrs = constrs})

addConstrs' :: (Monad m) => (Ref -> [ConstrRef]) -> KMonadE f v m Ref
addConstrs' f = do r <- freshRef; addConstrs (f r); return r

addConstr' :: (Monad m) => (Ref -> ConstrRef) -> KMonadE f v m Ref
addConstr' f = addConstrs' (return . f)

whnfM :: (Monad m, VarC v) => TmRef v -> KMonadE f v m (TmRef v)
whnfM t = (`whnf` t) <$> getEnv

nfM :: (Monad m, VarC v) => TmRef v -> KMonadE f v m (TmRef v)
nfM t = (`nf` t) <$> getEnv

slamM :: (VarC v, IsCursor c, Monad m) => Tm r v -> KMonad (c f) v m (TmId r)
slamM t = flip slam t <$> getEnv

formHoleM :: (VarC v, Monad m)
          => HoleId -> TmRef v -> [(TmRef v, TmRef v)]
          -> KMonadE f v m HoleCtx
formHoleM hn goal ts =
    do env <- getEnv
       r <- freshRef
       return (formHole (envCurs env) r hn goal ts)

mismatch :: (VarC v, Monad m, IsCursor c)
         => TmRef v -> TmRef v -> TmRef v -> KMonad (c f) v m a
mismatch t₁ t₂ t₃ =
    throwKError =<< Mismatch <$> slamM t₁ <*> slamM t₂ <*> slamM t₃

expectingType :: (VarC v, Monad m, IsCursor c)
              => TmRef v -> TmRef v -> KMonad (c f) v m a
expectingType t₁ t₂ = throwKError =<< ExpectingType <$> slamM t₁ <*> slamM t₂

expectingFunction :: (VarC v, Monad m, IsCursor c)
                  => Maybe (TmRef v) -> TmRef v -> KMonad (c f) v m a
expectingFunction tm t =
    do tm' <- case tm of Nothing -> return Nothing; Just t' -> Just <$> slamM t'
       throwKError =<< ExpectingFunction tm' <$> slamM t

expectingTypeData :: (VarC v, Monad m, IsCursor c)
                  => ConId -> ConId -> TmRefId -> KMonad (c f) v m a
expectingTypeData dc tyc ty = throwKError (ExpectingTypeData dc tyc ty)

wrongRecTypePos :: (VarC v, Monad m, IsCursor c)
                => ConId -> ConId -> TmRefId -> KMonad (c f) v m a
wrongRecTypePos dc tyc ty = throwKError (WrongRecTypePos dc tyc ty)

untypedTm :: (VarC v, Monad m, IsCursor c) => TmRef v -> KMonad (c f) v m a
untypedTm t = throwKError =<< UntypedTm <$> slamM t

unexpectedHole :: (Monad m) => HoleId -> KMonad f v m a
unexpectedHole hid = throwKError (UnexpectedHole hid)

cyclicTypes :: (Monad m) => KMonad f v m a
cyclicTypes = throwKError CyclicTypes

expectingTypeCon :: (VarC v, IsCursor c, Monad m)
                 => ConId -> TmRef v -> KMonad (c f) v m a
expectingTypeCon dc t = throwKError =<< ExpectingTypeCon dc <$> slamM t

duplicateName :: (Monad m) => Id -> KMonad f v m a
duplicateName = throwKError . DuplicateName

processModuleM :: (Monad m) => String -> KMonadE f Id m (Module Ref)
processModuleM = either (throwKError . TmParse) putRef . parseModule

processDeclM :: (Monad m) => String -> KMonadE f Id m (Decl Ref)
processDeclM = either (throwKError . TmParse) putRef . parseDecl

processTmM :: (Monad m) => String -> KMonadE f Id m TmRefId
processTmM = either (throwKError . TmParse) putRef . parseTm
