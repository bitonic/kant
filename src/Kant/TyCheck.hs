{-# LANGUAGE ViewPatterns #-}
module Kant.TyCheck
    ( TyCheckError(..)
    , TyCheckM
    , TyCheck(..)
    , tyCheckT
    ) where

import           Control.Applicative ((<$>), (<$))
import           Control.Monad (unless, forM_)

import           Control.Monad.Error (Error(..), MonadError(..))
import qualified Data.Set as Set

import           Bound
import           Bound.Name

import qualified Kant.Environment as Env
import           Kant.Environment hiding (envTy, addAbst, addVal, addData)
import           Kant.Reduce
import           Kant.Term

data TyCheckError
    = TyCheckError
    | OutOfBounds Id
    | DuplicateName Id
    | Mismatch Term Term Term
    | ExpectingFunction Term Term
    | ExpectingType Term Term
    | ExpectingCanonical Term Term
      -- TODO report if there are too few or too many branches
    | WrongBranchNumber Term
    | NotConstructor Branch
    | WrongArity Branch
    deriving (Eq, Show)

-- `envPull env v' will be consistent with whatever `pullTerm' returns since
-- outer bounds variables are the top level ones, and so the name will be
-- preserved.
outOfBounds :: EnvT a -> a -> TyCheckM b
outOfBounds env n = throwError (OutOfBounds (envPull env n))

mismatch :: Ord a => EnvT a -> TermT a -> TermT a -> TermT a -> TyCheckM b
mismatch env ty₁ t ty₂ =
    throwError (Mismatch (pullTerm env ty₁) (pullTerm env t) (pullTerm env ty₂))

expectingFunction, expectingType, expectingCanonical ::
     Ord a => EnvT a -> TermT a -> TermT a -> TyCheckM b
expectingFunction env t ty =
    throwError (ExpectingFunction (pullTerm env t) (pullTerm env ty))
expectingType env t ty =
    throwError (ExpectingType (pullTerm env t) (pullTerm env ty))
expectingCanonical env t ty =
    throwError (ExpectingType (pullTerm env t) (pullTerm env ty))

wrongBranchNumber :: Ord a => EnvT a -> TermT a -> TyCheckM b
wrongBranchNumber env t = throwError (WrongBranchNumber (pullTerm env t))

notConstructor :: Ord a => EnvT a -> BranchT a -> TyCheckM b
notConstructor env (c, i, s) = throwError (NotConstructor (c, i, pullTerm env s))

wrongArity :: Ord a => EnvT a -> BranchT a -> TyCheckM b
wrongArity env (c, i, s) = throwError (WrongArity (c, i, pullTerm env s))

instance Error TyCheckError where
    noMsg = TyCheckError

type TyCheckM = Either TyCheckError

nestTyCheckM :: EnvT a
             -> TScopeT a b
             -> (b -> TermT a)
             -> (EnvT (Var (Name Id b) a) -> TermT (Var (Name Id b) a) -> TyCheckM c)
             -> TyCheckM c
nestTyCheckM env s ty f = f (nestEnv' env (Just . ty)) (fromScope s)

class TyCheck a where
    tyCheck :: Env -> a -> TyCheckM Env

instance TyCheck Module where
    tyCheck env' (Module decls') = go decls' env'
      where
        go []             env = Right env
        go (decl : decls) env = tyCheck env decl >>= go decls

instance TyCheck Decl where
    tyCheck env (ValD val)      = tyCheck env val
    tyCheck env (DataD dat)      = tyCheck env dat
    tyCheck env (Postulate n t) =
        case Env.envTy env n of
            Just _ -> throwError (DuplicateName n)
            _      -> addAbst env n t

instance TyCheck Val where
    tyCheck env vd@(Val _ ty t) =
        do env' <- addVal env vd
           env' <$ tyCheckEq env' ty t

instance TyCheck Data where
    tyCheck env dd =
        do let ((c, (ty, _)), cons) = dataDecl dd
           tyCheckT env ty
           env' <- addAbst env c ty
           mapM_ (tyCheckT env') (map (\(_, (ty', _)) -> ty') cons)
           addData env dd

dupMaybe :: Id -> Maybe b -> TyCheckM b
dupMaybe _ (Just x) = return x
dupMaybe n Nothing  = throwError (DuplicateName n)

addAbst :: Env -> Id -> Term -> TyCheckM Env
addAbst env n t = dupMaybe n (Env.addAbst env n t)

addVal :: Env -> Val -> TyCheckM Env
addVal env vd@(Val n _ _) = dupMaybe n (Env.addVal env vd)

addData :: Env -> Data -> TyCheckM Env
addData env dd = either (throwError . DuplicateName) return (Env.addData env dd)

envTy :: Eq a => EnvT a -> a -> TyCheckM (TermT a)
envTy env v = maybe (outOfBounds env v) return (Env.envTy env v)

tyCheckT :: Ord a => EnvT a -> TermT a -> TyCheckM (TermT a)
tyCheckT env (Var v) = envTy env v
tyCheckT _ (Type l) = return (Type (l + 1))
-- TODO we manually have a "large" arrow here, but ideally we'd like to have
-- some kind of level polymorphism so that the arrow operator can be postulated
-- like any other.
tyCheckT env (Arr ty s) =
    do ty' <- tyCheckT env ty
       case nf env ty' of
           Type l₁ ->
               do let env' = nestEnv' env (const (Just ty))
                  tys <- tyCheckT env' (fromScope s)
                  case nf env' tys of
                      Type l₂ -> return (Type (max l₁ l₂))
                      _       -> expectingType env' (fromScope s) tys
           _ -> expectingType env ty ty'
tyCheckT env (App t₁ t₂) =
    do ty₁ <- tyCheckT env t₁
       case nf env ty₁ of
           Arr ty₂ s -> instantiate1 t₂ s <$ tyCheckEq env ty₂ t₂
           _         -> expectingFunction env t₁ ty₁
tyCheckT env (Lam ty s) =
    do tyCheckT env ty
       tys <- toScope <$> nestTyCheckM env s (const ty) tyCheckT
       return (Arr ty tys)
tyCheckT env@Env{envNest = nest} (Constr c pars args) =
    tyCheckT env (app (Var (nest c) : pars ++ args))
tyCheckT env@Env{envNest = nest} ct@(Case t@(Var v) ty₁ brs) = undefined

tyCheckT _ (Case _ _ _) =
    error "tyCheckT got a case with a non-variable, this should not happen"

-- | @tyCheckEq ty t@ thecks that the term @t@ has type @ty@.
tyCheckEq :: Ord a => EnvT a -> TermT a -> TermT a -> TyCheckM ()
tyCheckEq env ty t =
    do ty' <- tyCheckT env t
       unless (eqCum env ty' ty) (mismatch env ty t ty')

-- | @'eqCum' ty₁ ty₂@ checks if ty₁ is equal to ty₂, including cumulativity.
--   For example @'eqCum' ('Type' 1) ('Type' 4)@ will succeed, but @'eqCum'
--   ('Type' 4) ('Type' 1)@ will fail.
eqCum :: Ord a => EnvT a -> TermT a -> TermT a -> Bool
eqCum env (nf env -> Type l₁) (nf env -> Type l₂) = l₁ <= l₂
eqCum env (nf env -> ty₁)     (nf env -> ty₂)     = ty₁ == ty₂
