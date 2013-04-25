{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
module Kant.Monad
    ( -- * Kant 'Monad'
      KError(..)
    , KMonad(KMonad)
    , runKMonad
    , mapKMonad
    , throwKError
      -- * Environment actions
    , getEnv
    , putEnv
    , nestEnvM
    , nestEnvTyM
    , lookupTy
    , addFreeM
    , addADTM
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
    , untypedTerm
    , unexpectedHole
    , cyclicTypes
    , expectingTypeCon
    , duplicateName
      -- * Parsing
    , parseModuleM
    , parseDeclM
    , parseTermM
    ) where

import           Control.Applicative (Applicative)

import           Control.Monad.Error (Error, ErrorT(..), throwError, mapErrorT)
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.State (StateT(..), put, get, mapStateT)
import           Control.Monad.Trans.Class (MonadTrans(..))
import qualified Text.Parsec as Parsec

import           Bound

import qualified Data.Constraint as Constr
import           Kant.Common
import           Kant.Term
import           Kant.ADT
import           Kant.Env
import           Kant.Uniquify
import           Kant.Reduce
import           Kant.Parser
import           Kant.Decl

data KError
    = OutOfBounds Id
    | DuplicateName Id
    | Mismatch TermRefId TermRefId TermRefId
    | ExpectingFunction TermRefId TermRefId
    | ExpectingType TermRefId TermRefId
    | ExpectingTypeCon ConId TermRefId
    | ExpectingTypeData ConId ConId TermRefId
    | WrongRecTypePos ConId ConId TermRefId
    | UntypedTerm TermRefId
    | UnexpectedHole HoleId
    | CyclicTypes               -- TODO more descriptive
      -- REPL errors
    | CmdParse Parsec.ParseError
    | TermParse ParseError
    | IOError IOError
    deriving (Show)

instance Error KError

newtype KMonad v m a = KMonad {runKMonad' :: StateT (Env v) (ErrorT KError m) a}
    deriving (Functor, Applicative, Monad)

instance MonadTrans (KMonad v) where
    lift m = KMonad (lift (lift m))

instance MonadIO m => MonadIO (KMonad v m) where
    liftIO = KMonad . liftIO

runKMonad :: Env v -> KMonad v m a -> m (Either KError (a, Env v))
runKMonad env = runErrorT . (`runStateT` env) . runKMonad'

mapKMonad :: (m (Either KError (a, Env v)) -> n (Either KError (b, Env v)))
          -> KMonad v m a -> KMonad v n b
mapKMonad f = KMonad . mapStateT (mapErrorT f) . runKMonad'

throwKError :: Monad m => KError -> KMonad v m a
throwKError = KMonad . throwError

getEnv :: Monad m => KMonad v m (Env v)
getEnv = KMonad get

putEnv :: Monad m => Env v -> KMonad v m ()
putEnv env = KMonad (put env)

-- | Enters a scope with a certain value and type, runs an action on that new
--   scope, and returns back to the outer scope.
nestEnvM :: Monad m
         => Maybe (TermRef v) -> Maybe (TermRef v)
         -> KMonad (Var (NameId ()) v) m a -> KMonad v m a
nestEnvM t ty (KMonad m) =
    KMonad $ StateT $
    \env -> do (x, env') <- runStateT m (nestEnv env t ty)
               return (x, env'{ envValue  = envValue env
                              , envType   = envType env
                              , envPull   = envPull env
                              , envNest   = envNest env
                              , envRename = envRename env
                              })

nestEnvTyM :: Monad m => TermRef v -> KMonad (Var (NameId ()) v) m a -> KMonad v m a
nestEnvTyM ty = nestEnvM Nothing (Just ty)

lookupTy :: (VarC v, Monad m) => v -> KMonad v m (TermRef v)
lookupTy v =
    do env <- getEnv
       case envType env v of
           Nothing -> KMonad (throwError (OutOfBounds (envPull env v)))
           Just ty -> return ty

addFreeM :: (VarC v, Monad m)
         => v -> Maybe (TermRef v) -> Maybe (TermRef v) -> KMonad v m ()
addFreeM v mv mty = do env <- getEnv; putEnv (addFree env v mv mty)

addADTM :: (Monad m) => Id -> ADT -> KMonad v m ()
addADTM n adt = do env <- getEnv; putEnv (addADT env n adt)

freshRef :: (Monad m) => KMonad v m Ref
freshRef = do env <- getEnv; envRef env <$ putEnv (env{envRef = envRef env + 1})

addConstrs :: (Monad m) => [ConstrRef] -> KMonad v m ()
addConstrs cs =
    do env <- getEnv
       constrs <- maybe cyclicTypes return (Constr.addConstrs cs (envConstrs env))
       putEnv (env{envConstrs = constrs})

addConstrs' :: (Monad m) => (Ref -> [ConstrRef]) -> KMonad v m Ref
addConstrs' f = do r <- freshRef; addConstrs (f r); return r

addConstr' :: (Monad m) => (Ref -> ConstrRef) -> KMonad v m Ref
addConstr' f = addConstrs' (return . f)

whnfM :: (Monad m, VarC v) => TermRef v -> KMonad v m (TermRef v)
whnfM t = (`whnf` t) <$> getEnv

nfM :: (Monad m, VarC v) => TermRef v -> KMonad v m (TermRef v)
nfM t = (`nf` t) <$> getEnv

slamM :: (VarC v, Monad m) => Term r v -> KMonad v m (TermId r)
slamM t = flip slam t <$> getEnv

formHoleM :: (VarC v, Monad m)
          => HoleId -> TermRef v -> [(TermRef v, TermRef v)]
          -> KMonad v m HoleCtx
formHoleM hn goal ts =
    do env <- getEnv
       r <- freshRef
       return (formHole env r hn goal ts)

mismatch :: (VarC v, Monad m) => TermRef v -> TermRef v -> TermRef v -> KMonad v m a
mismatch t₁ t₂ t₃ =
    throwKError =<< Mismatch <$> slamM t₁ <*> slamM t₂ <*> slamM t₃

expectingType :: (VarC v, Monad m) => TermRef v -> TermRef v -> KMonad v m a
expectingType t₁ t₂ = throwKError =<< ExpectingType <$> slamM t₁ <*> slamM t₂

expectingFunction :: (VarC v, Monad m) => TermRef v -> TermRef v -> KMonad v m a
expectingFunction t₁ t₂ = throwKError =<< ExpectingFunction <$> slamM t₁ <*> slamM t₂

expectingTypeData :: (VarC v, Monad m)
                  => ConId -> ConId -> TermRef v -> KMonad v m a
expectingTypeData dc tyc ty = throwKError =<< ExpectingTypeData dc tyc <$> slamM ty

wrongRecTypePos :: (VarC v, Monad m)
                => ConId -> ConId -> TermRef v -> KMonad v m a
wrongRecTypePos dc tyc ty = throwKError =<< WrongRecTypePos dc tyc <$> slamM ty

untypedTerm :: (VarC v, Monad m) => TermRef v -> KMonad v m a
untypedTerm t = throwKError =<< UntypedTerm <$> slamM t

unexpectedHole :: (Monad m) => HoleId -> KMonad v m a
unexpectedHole hid = KMonad (throwError (UnexpectedHole hid))

cyclicTypes :: (Monad m) => KMonad v m a
cyclicTypes = KMonad (throwError CyclicTypes)

expectingTypeCon :: (VarC v, Monad m) => ConId -> TermRef v -> KMonad v m a
expectingTypeCon dc t = throwKError =<< ExpectingTypeCon dc <$> slamM t

duplicateName :: (VarC v, Monad m) => v -> KMonad v m a
duplicateName v = throwKError =<< DuplicateName <$> ((`envPull` v) <$> getEnv)

parseModuleM :: (Monad m) => String -> KMonad v m ModuleSyn
parseModuleM = either (throwKError . TermParse) return . parseModule

parseDeclM :: (Monad m) => String -> KMonad v m DeclSyn
parseDeclM = either (throwKError . TermParse) return . parseDecl

parseTermM :: (Monad m) => String -> KMonad v m TermSyn
parseTermM = either (throwKError . TermParse) return . parseTerm
