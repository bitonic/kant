{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
module Kant.TyCheck
    ( TyCheckError(..)
    , MonadTyCheck
    , TyCheck(..)
    , tyCheckT
    )
    where

import           Control.Applicative ((<$), (<$>), Applicative)
import           Control.Monad (unless, forM_)

import           Control.Monad.Error (Error(..), MonadError(..), ErrorT)
import           Control.Monad.State (MonadState(..), StateT)
import qualified Data.Set as Set

import           Kant.Name
import           Kant.Environment hiding (envTy)
import qualified Kant.Environment as Env
import           Kant.Reduce
import           Kant.Term

data TyCheckError
    = TyCheckError
    | OutOfBounds TName
    | DuplicateName TName
    | Mismatch Term Term Term
    | ExpectingFunction Term Term
    | ExpectingType Term Term
    | ExpectingCanonical Term Term
      -- TODO report if there are too few or too many branches
    | WrongBranchNumber Term
    | NotConstructor ConId Term
    | WrongArity ConId Term
    deriving (Eq, Show)

instance Error TyCheckError where
    noMsg = TyCheckError

class (MonadEnv m, MonadError TyCheckError m, Functor m, Applicative m) =>
      MonadTyCheck m
instance (Monad m, Functor m, Applicative m) =>
         MonadTyCheck (ErrorT TyCheckError (StateT Env m))
instance (Monad m, Functor m, Applicative m) =>
         MonadTyCheck (StateT Env (ErrorT TyCheckError m))

class TyCheck a where
    tyCheck :: MonadTyCheck m => a -> m ()

checkDup :: MonadTyCheck m => Id -> m Bool -> m ()
checkDup n m = do b <- m
                  unless b (throwError (DuplicateName (free n)))

instance (v ~ TName) => TyCheck (ModuleT v) where
    tyCheck (Module decls') = mapM_ tyCheck decls'

instance (v ~ TName) => TyCheck (DeclT v) where
    -- TODO we are tychecking before verifying that there are no duplicates
    tyCheck (Val n t) = do t' <- nf t
                           ty <- tyCheckT t'
                           checkDup n (addVal (free n) ty t')
    tyCheck (Postulate n ty) = do tyCheckT ty; checkDup n (addAbst (free n) ty)
    tyCheck (Data c dd@(Tele pars (DataT l cons))) =
        -- TODO finish
        addData c dd (DuplicateName . free)

-- forget :: MonadState s m => m b -> m b
-- forget m = do s <- get; x <- m; put s; return x
forget b ty₁ m = do upAbst b ty₁
                    x <- m
                    delCtx b
                    return x

envTy :: MonadTyCheck m => TName -> m Term
envTy v = maybe (throwError (OutOfBounds v)) return =<< Env.envTy v

tyCheckT :: MonadTyCheck m => Term -> m Term
tyCheckT (Var v) = envTy v
tyCheckT (Type l) = return (Type (l + 1))
-- TODO we manually have a "large" arrow here, but ideally we'd like to have
-- some kind of level polymorphism so that the arrow operator can be postulated
-- like any other.
tyCheckT (Arr ty₁ (Scope b ty₂)) =
    do tyty₁ <- tyCheckT ty₁
       tyty₁' <- nf tyty₁
       case tyty₁' of
           Type l₁ -> forget b ty₁ $
                      do tyty₂ <- tyCheckT ty₂
                         tyty₂' <- nf tyty₂
                         case tyty₂' of
                             Type l₂ -> return (Type (max l₁ l₂))
                             _       -> throwError (ExpectingType ty₂ tyty₂)
           _ -> throwError (ExpectingType ty₁ tyty₁)
tyCheckT (App t₁ t₂) =
    do ty₁ <- tyCheckT t₁
       ty₁' <- nf ty₁
       case ty₁' of
           Arr ty₂ (Scope b ty₃) -> do tyCheckEq ty₂ t₂; substB b t₂ ty₃
           _                     -> throwError (ExpectingFunction t₁ ty₁)
tyCheckT (Lam ty (Scope b t)) =
    do tyty <- tyCheckT ty
       tyty' <- nf tyty
       case tyty' of
           Type _ -> forget b ty $
                     do tyt <- tyCheckT t
                        return (Arr ty (Scope b tyt))
           _ -> throwError (ExpectingType ty tyty)
tyCheckT (Constr c pars args) =
    tyCheckT (app (Var (free c) : pars ++ args))
tyCheckT (Fix (Tele pars (FixT ty (Scope b t)))) =
    -- TODO finish
     do let ty' = pis pars ty
        tyCheckT ty'
        return ty'
tyCheckT ct@(Case t (Scope b ty) brs) =
    do tyt <- tyCheckT t
       forget b tyt (tyCheckT ty)
       tyt' <- nf tyt
       case unrollApp tyt' of
           (Var (Plain tyc), args) ->
               do dd <- envData' tyc
                  case dd of
                      Just (Tele pars (DataT _ cons)) | length pars == length args ->
                          if length brs /= Set.size (Set.fromList (map fst brs))
                          then throwError (WrongBranchNumber ct)
                          else do forM_ brs (checkBr (zip (map fst pars) args) cons)
                                  substB b t ty
                      _ -> canon tyt
           _ -> canon tyt'
  where
    canon = throwError . ExpectingCanonical t
    checkBr parsty cons (c, Tele (branchBs -> bs) t') = return ()
        -- case [parsd | ConstrT c' (Tele parsd Proxy) <- cons, c == c'] of
        --     [] -> throwError (NotConstructor c ct)
        --     (parsd:_) | length parsd == length bs ->
        --         do -- First, we substitute the type parameters with the actual
        --            -- ones in the data parameters
        --            parsd₁ <- sequence [substManyB parsty ty' | (_, ty') <- parsd]
        --            -- Then, we substitute the parameters names with the names
        --            -- given by the branch.  First we make sure that each
        --            -- parameter has a name
        --            bs' <- fillNames bs
        --            let vs = zip (map fst parsd) [Var ta | Just ta <- bs']
        --            -- Then we replace the references to data parameters
        --            parsd₂ <- sequence [ (b',) <$> substManyB vs ty'
        --                               | (b', ty') <- zip bs' parsd₁ ]
        --            -- We put all the matched variables in the context
        --            sequence [upAbst' b' ty' | (b', ty') <- parsd₂]
        --            -- Finally, we replace the abstracted variable with the
        --            -- refined variable
        --            let ref = Constr c (map snd parsty) (map snd parsd₂)
        --            (`tyCheckEq`  t') =<< substB b ref ty
        --            -- and we remove the vars from the ctx
        --            sequence [delCtx' b' | (b', _) <- parsd₂]
        --     _ -> throwError (WrongArity c ct)

-- | @tyCheckEq ty t@ thecks that the term @t@ has type @ty@.
tyCheckEq :: MonadTyCheck m => Term -> Term -> m ()
tyCheckEq ty t =
    do ty' <- tyCheckT t
       eqb <- eqCum ty' ty
       unless eqb (throwError (Mismatch ty t ty'))

-- | @'eqCum' ty₁ ty₂@ checks if ty₁ is equal to ty₂, including cumulativity.
--   For example @'eqCum' ('Type' 1) ('Type' 4)@ will succeed, but @'eqCum'
--   ('Type' 4) ('Type' 1)@ will fail.
eqCum :: MonadEnv m => Term -> Term -> m Bool
eqCum t₁ t₂ = do t₁' <- nf t₁; t₂' <- nf t₂
                 return $ case (t₁', t₂') of
                              (Type l₁, Type l₂) -> l₁ <= l₂
                              _                  -> t₁' == t₂'
