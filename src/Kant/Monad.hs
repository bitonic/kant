{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Kant.Monad
    ( -- * Kant 'Monad'
      KError(..)
    , KMonadT
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
    , nestM
    , nestPM
    , lookupTy
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
    , parseModuleM
    , parseDeclM
    , parseTmM
    ) where

import           Control.Applicative (Applicative)
import           Control.Arrow (second)

import           Control.Monad.Error (Error, ErrorT(..), throwError, mapErrorT)
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.State (StateT(..), put, get, mapStateT)
import           Control.Monad.Trans.Class (MonadTrans(..))
import qualified Text.Parsec as Parsec

import           Bound
import           Data.Proxy

import qualified Data.Constraint as Constr
import           Kant.ADT
import           Kant.Common
import           Kant.Cursor
import           Kant.Decl
import           Kant.Env
import           Kant.Parser
import           Kant.Reduce
import           Kant.Term
import           Kant.Uniquify

data KError
    = OutOfBounds Id
    | DuplicateName Id
    | Mismatch TmRefId TmRefId TmRefId
    | ExpectingFunction TmRefId TmRefId
    | ExpectingType TmRefId TmRefId
    | ExpectingTypeCon ConId TmRefId
    | ExpectingTypeData ConId ConId TmRefId
    | WrongRecTypePos ConId ConId TmRefId
    | UntypedTm TmRefId
    | UnexpectedHole HoleId
    | CyclicTypes               -- TODO more descriptive
      -- REPL errors
    | CmdParse Parsec.ParseError
    | TmParse ParseError
    | IOError IOError
    deriving (Show)

instance Error KError

newtype KMonad f v m a = KMonad {runKMonad' :: StateT (f v) (ErrorT KError m) a}
    deriving (Functor, Applicative, Monad)
type KMonadP = KMonad (Env Proxy)
type KMonadT = KMonad (Env TmRef)
type KMonadE f = KMonad (Env f)

instance MonadTrans (KMonad f v) where
    lift m = KMonad (lift (lift m))

instance MonadIO m => MonadIO (KMonad f v m) where
    liftIO = KMonad . liftIO

runKMonad :: f v -> KMonad f v m a -> m (Either KError (a, f v))
runKMonad env = runErrorT . (`runStateT` env) . runKMonad'

mapKMonad :: (m (Either KError (a, f v)) -> n (Either KError (b, f v)))
          -> KMonad f v m a -> KMonad f v n b
mapKMonad f = KMonad . mapStateT (mapErrorT f) . runKMonad'

fromKMonadP :: (IsCursor c, Monad m) => KMonad (c Proxy) v m a -> KMonad (c f) v m a
fromKMonadP (KMonad (StateT f)) =
    KMonad $ StateT $ \env -> second (restoreC env) <$> f (toP env)

throwKError :: Monad m => KError -> KMonad f v m a
throwKError = KMonad . throwError

getEnv :: Monad m => KMonad f v m (f v)
getEnv = KMonad get

putEnv :: Monad m => f v -> KMonad f v m ()
putEnv env = KMonad (put env)

-- | Enters a scope with a certain value and type, runs an action on that new
--   scope, and returns back to the outer scope.
nestM :: (Monad m, IsCursor c, Functor f)
      => f v -> KMonad (c f) (Var (NameId ()) v) m a -> KMonad (c f) v m a
nestM ty (KMonad m) =
    KMonad (StateT (\env -> second (restoreC env) <$> runStateT m (nestC env ty)))

nestPM :: (Monad m, IsCursor c)
       => KMonad (c Proxy) (Var (NameId ()) v) m a -> KMonad (c Proxy) v m a
nestPM = nestM Proxy

lookupTy :: (VarC v, Monad m) => v -> KMonadT v m (TmRef v)
lookupTy v =
    do env <- getEnv
       case envType env v of
           Nothing -> KMonad (throwError (OutOfBounds (pull env v)))
           Just ty -> return ty

addFreeM :: (VarC v, Monad m) => Id -> TmRefId -> Maybe TmRefId -> KMonadT v m ()
addFreeM v ty mv = do env <- getEnv; putEnv (addFree env v ty mv)

addADTM :: (Monad m) => ConId -> ADT -> KMonadT v m ()
addADTM n adt = do env <- getEnv; putEnv (addADT env n adt)

addRecM :: (Monad m) => ConId -> Record -> KMonadT v m ()
addRecM n rec = do env <- getEnv; putEnv (addRec env n rec)

freshRef :: (Monad m) => KMonadE f v m Ref
freshRef = do env <- getEnv; envRef env <$ putEnv (env{envRef = envRef env + 1})

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
                  => TmRef v -> TmRef v -> KMonad (c f) v m a
expectingFunction t₁ t₂ = throwKError =<< ExpectingFunction <$> slamM t₁ <*> slamM t₂

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

parseModuleM :: (Monad m) => String -> KMonad f v m ModuleSyn
parseModuleM = either (throwKError . TmParse) return . parseModule

parseDeclM :: (Monad m) => String -> KMonad f v m DeclSyn
parseDeclM = either (throwKError . TmParse) return . parseDecl

parseTmM :: (Monad m) => String -> KMonad f v m TmSyn
parseTmM = either (throwKError . TmParse) return . parseTm
