{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module Kant.TyCheck
    ( TyCheckError(..)
    , TyCheckM
    , TyCheck(..)
    , tyCheck'
    , basicEnv
    ) where

import           Control.Applicative ((<$>), (<$))
import           Control.Monad (unless)

import           Control.Monad.Error (Error(..), MonadError(..))

import           Bound
import           Bound.Name

import qualified Kant.Environment as Env
import           Kant.Environment hiding (lookupTy, addAbst, addVal)
import           Kant.Reduce
import           Kant.Syntax

data TyCheckError
    = TyCheckError
    | OutOfBounds Id
    | DuplicateName Id
    | Mismatch Term Term Term
    | ExpectingFunction Term Term
    deriving (Eq, Show)

instance Error TyCheckError where
    noMsg = TyCheckError

type TyCheckM = Either TyCheckError

nestTyCheckM :: EnvT a
             -> TScopeT a b
             -> TermT a
             -> (EnvT (Var (Name Id b) a) -> TermT (Var (Name Id b) a) -> TyCheckM c)
             -> TyCheckM c
nestTyCheckM env s ty f = f (nestEnv env (Just ty)) (fromScope s)

class TyCheck a where
    tyCheck :: Env -> a -> TyCheckM Env

instance TyCheck Module where
    tyCheck env' (Module decls') = go decls' env'
      where
        go []             env = Right env
        go (decl : decls) env = tyCheck env decl >>= go decls

instance TyCheck Decl where
    tyCheck env (ValDecl val)   = tyCheck env val
    tyCheck env (Postulate n t) =
        case Env.lookupTy env n of
            Just _ -> throwError (DuplicateName n)
            _      -> addAbst env n t
    tyCheck env (DataDecl dat)  = tyCheck env dat

instance TyCheck Val where
    tyCheck env vd@(Val _ ty t) =
        do env' <- addVal env vd
           env' <$ tyCheckEq env' ty t

instance TyCheck Data where
    tyCheck _ _ = undefined

-- -- Some overloaded versions...

addAbst :: Eq a => EnvT a -> a -> TermT a -> TyCheckM (EnvT a)
addAbst env n t = maybe (throwError (DuplicateName (envPull env n))) return
                        (Env.addAbst env n t)

addVal :: Env -> Val -> TyCheckM Env
addVal env vd@(Val n _ _) = maybe (throwError (DuplicateName (envPull env n))) return
                                  (Env.addVal env vd)


-- addData :: Data -> TyCheckM Id Env
-- addData dd = do env <- ask
--                 either (throwError . DuplicateName) return
--                        (Env.addData env dd)

lookupTy :: Eq a => EnvT a -> a -> TyCheckM (TermT a)
lookupTy env v = case Env.lookupTy env v of
                     Nothing -> throwError (OutOfBounds (Env.envPull env v))
                     Just ty -> return ty

tyCheck' :: Ord a => EnvT a -> TermT a -> TyCheckM (TermT a)
-- `envPull env v' will be consistent with whatever `pullTerm' returns since
-- outer bounds variables are the top level ones, and so the name will be
-- preserved.
tyCheck' env (Var v)      = lookupTy env v
tyCheck' _   (Type l)     = return (Type (l + 1))
tyCheck' env (App t₁ t₂)  =
    do ty₁ <- tyCheck' env t₁
       case arrV (envNest env) (nf env ty₁) of
           IsArr ty₂ s -> instantiate1 t₂ s <$ tyCheckEq env ty₂ t₂
           NoArr       -> throwError $
                          ExpectingFunction (pullTerm env t₁) (pullTerm env ty₁)
tyCheck' env (Lam ty s)   =
    do let ar = envNest env <$> arrow
       tyCheck' env ty
       tys <- toScope <$> nestTyCheckM env s ty tyCheck'
       return (App (App ar ty) (Lam ty tys))
tyCheck' _ (Case _ _) = undefined

-- | @tyCheckEq ty t@ thecks that the term @t@ has type @ty@.
tyCheckEq :: Ord a => EnvT a -> TermT a -> TermT a -> TyCheckM ()
tyCheckEq env ty t =
    do ty' <- tyCheck' env t
       unless (defeq env ty ty')
              (throwError (Mismatch (pullTerm env ty) (pullTerm env t)
                                    (pullTerm env ty')))

-- TODO make this large
basicEnv :: Env
basicEnv = Env.newEnv $ \n -> if n == "(->)"
                              then Just (Abstract arrty)
                              else Nothing
  where arrty = pis [("A", Type 0), ("B", arr (Var "A") (Type 0))] (Type 0)
