{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module Kant.TyCheck where

import           Control.Applicative (Applicative(..), (<$>), (<$))
import           Control.Monad (unless)

import           Control.Monad.Reader (ReaderT(..), MonadReader(..), asks, runReaderT)
import           Control.Monad.Error (Error(..), MonadError(..))

import           Bound
import           Bound.Name

import           Kant.Syntax
import           Kant.Environment
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
    TyCheckM . ReaderT $ runReaderT (unTyCheckM (f (fromScope s))) . nestEnv

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
           case lookupTy n env of
               Just _ -> throwError (DuplicateName n)
               _      -> addAbst' n t
    tyCheck (DataDecl dat)  = tyCheck dat

instance TyCheck Val

instance TyCheck Data

-- Some overloaded versions...

addAbst' :: Eq a => a -> TermT a -> TyCheckM a (EnvT a)
addAbst' n t = do env <- ask; return (addAbst env n t)

lookupTy' :: Eq a => a -> TyCheckM a (TermT a)
lookupTy' v = do env <- ask
                 case lookupTy v env of
                     Nothing -> throwError (OutOfBounds (envPull env v))
                     Just ty -> return ty

pullTerm' :: Ord a => TermT a -> TyCheckM a Term
pullTerm' t = do env <- ask; return (pullTerm env t)

nf :: Eq a => TermT a -> TyCheckM a (TermT a)
nf t = do env <- ask; return (Reduce.nf env t)

defeq :: Eq a => TermT a -> TermT a -> TyCheckM a Bool
defeq t₁ t₂ = do env <- ask; return (Reduce.defeq env t₁ t₂)

tyCheck' :: Ord a => TermT a -> TyCheckM a (TermT a)
-- `envPull env v' will be consistent with whatever `pullTerm' returns since
-- outer bounds variables are the top level ones, and so the name will be
-- preserved.
tyCheck' (Var v)      = lookupTy' v
tyCheck' (Type l)     = return (Type (l + 1))
tyCheck' (App t₁ t₂)  =
    do ty₁ <- tyCheck' t₁
       ar <- arrV <$> asks envNest <*> nf ty₁
       case ar of
           IsArr ty₂ s -> instantiate1 t₂ s <$ tyCheckEq ty₂ t₂
           NoArr       -> throwError =<<
                          ExpectingFunction <$> pullTerm' t₂
                                            <*> (tyCheck' t₂ >>= pullTerm')
tyCheck' (Lam ty s)   =
    do ar <- (<$> arrow) <$> asks envNest
       tyCheck' ty
       tys <- toScope <$> nestTyCheckM s tyCheck'
       return (App (App ar ty) (Lam ty tys))
tyCheck' (Case t brs) = undefined

-- | @tyCheckEq ty t@ thecks that the term @t@ has type @ty@.
tyCheckEq :: Ord a => TermT a -> TermT a -> TyCheckM a ()
tyCheckEq ty t =
    do ty' <- tyCheck' t
       b <- defeq ty ty'
       unless b (throwError =<< Mismatch <$> pullTerm' ty <*> pullTerm' ty')