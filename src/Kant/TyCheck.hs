{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module Kant.TyCheck
    ( TyCheckError(..)
    , TyCheckM
    , TyCheck(..)
    ) where

import           Control.Applicative (Applicative(..), (<$>), (<$))
import           Control.Monad (unless)
import           Data.Maybe (fromMaybe)
import           Data.Traversable (traverse)

import           Control.Monad.Error (Error(..), MonadError(..))
import           Control.Monad.Reader (ReaderT(..), MonadReader(..), asks, runReaderT)
import           Control.Monad.Trans (lift)

import           Bound
import           Bound.Name

import           Kant.Syntax
import           Kant.Environment (EnvT, Env, NestT, PullT)
import qualified Kant.Environment as Env
import qualified Kant.Reduce as Reduce

data TyCheckError
    = TyCheckError
    | OutOfBounds Id
    | DuplicateName Id
    | Mismatch Term Term
    | ExpectingFunction Term Term

instance Error TyCheckError where
    noMsg = TyCheckError

newtype TyCheckM b a =
    TyCheckM {unTyCheckM :: ReaderT (EnvT b) (Either TyCheckError) a}
    deriving (Functor, Applicative, Monad)

nestTyCheckM :: TScopeT a b
             -> (TermT (Var (Name Id b) a) -> TyCheckM (Var (Name Id b) a) c)
             -> TyCheckM a c
nestTyCheckM s f =
    TyCheckM . ReaderT $
    runReaderT (unTyCheckM (f (fromScope s))) . Env.nestEnv

instance MonadReader (EnvT a) (TyCheckM a) where
    ask = TyCheckM ask
    local f (TyCheckM m) = TyCheckM (local f m)

instance MonadError TyCheckError (TyCheckM a) where
    throwError e = TyCheckM (throwError e)
    catchError (TyCheckM m) h = TyCheckM (catchError m (unTyCheckM . h))


class TyCheck a where
    tyCheck :: a -> TyCheckM Id Env

instance TyCheck Decl where
    tyCheck (ValDecl val)   = tyCheck val
    tyCheck (Postulate n t) =
        do env <- ask
           case Env.lookupTy n env of
               Just _ -> throwError (DuplicateName n)
               _      -> addAbst n t
    tyCheck (DataDecl dat)  = tyCheck dat

instance TyCheck Val where
    tyCheck vd@(Val _ ty t) =
        do env <- addVal vd
           TyCheckM (lift (runReaderT (unTyCheckM (tyCheckEq ty t)) env))
           return env

instance TyCheck Data where
    tyCheck dd =
        do env <- addData dd
           undefined -- TyCheckM (lift (runReaderT (unTyCheckM (tyCheckEq ty t)) env))
           return env

-- Some overloaded versions...

addAbst :: Eq a => a -> TermT a -> TyCheckM a (EnvT a)
addAbst n t = do env <- ask
                 maybe (throwError =<< DuplicateName <$> pull n) return
                       (Env.addAbst env n t)

addVal :: Val -> TyCheckM Id Env
addVal vd@(Val n _ _) = do env <- ask
                           maybe (throwError =<< DuplicateName <$> pull n) return
                                 (Env.addVal env vd)


addData :: Data -> TyCheckM Id Env
addData dd = do env <- ask
                either (throwError . DuplicateName) return
                       (Env.addData env dd)

lookupTy :: Eq a => a -> TyCheckM a (TermT a)
lookupTy v = do env <- ask
                case Env.lookupTy v env of
                    Nothing -> throwError (OutOfBounds (Env.envPull env v))
                    Just ty -> return ty

pullTerm :: Ord a => TermT a -> TyCheckM a Term
pullTerm t = do env <- ask; return (Env.pullTerm env t)

nest' :: TyCheckM a (NestT a)
nest' = asks Env.envNest

nest :: Id -> TyCheckM a a
nest n = nest' <*> return n

pull' :: TyCheckM a (PullT a)
pull' = asks Env.envPull

pull :: a -> TyCheckM a Id
pull n = pull' <*> return n

-- /

nf :: Eq a => TermT a -> TyCheckM a (TermT a)
nf t = do env <- ask; return (Reduce.nf env t)

defeq :: Eq a => TermT a -> TermT a -> TyCheckM a Bool
defeq t₁ t₂ = do env <- ask; return (Reduce.defeq env t₁ t₂)

tyCheck' :: Ord a => TermT a -> TyCheckM a (TermT a)
-- `envPull env v' will be consistent with whatever `pullTerm' returns since
-- outer bounds variables are the top level ones, and so the name will be
-- preserved.
tyCheck' (Var v)      = lookupTy v
tyCheck' (Type l)     = return (Type (l + 1))
tyCheck' (App t₁ t₂)  =
    do ty₁ <- tyCheck' t₁
       ar <- arrV <$> nest' <*> nf ty₁
       case ar of
           IsArr ty₂ s -> instantiate1 t₂ s <$ tyCheckEq ty₂ t₂
           NoArr       -> throwError =<<
                          ExpectingFunction <$> pullTerm t₂
                                            <*> (tyCheck' t₂ >>= pullTerm)
tyCheck' (Lam ty s)   =
    do ar <- traverse nest arrow
       tyCheck' ty
       tys <- toScope <$> nestTyCheckM s tyCheck'
       return (App (App ar ty) (Lam ty tys))
tyCheck' (Case t brs) = undefined

-- | @tyCheckEq ty t@ thecks that the term @t@ has type @ty@.
tyCheckEq :: Ord a => TermT a -> TermT a -> TyCheckM a ()
tyCheckEq ty t =
    do ty' <- tyCheck' t
       b <- defeq ty ty'
       unless b (throwError =<< Mismatch <$> pullTerm ty <*> pullTerm ty')
