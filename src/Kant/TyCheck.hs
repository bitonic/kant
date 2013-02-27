{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.TyCheck
    ( TyCheckError(..)
    , MonadTyCheck
    , TyCheck(..)
    , tyCheckT
    )
    where

import           Control.Applicative (Applicative)
import           Control.Monad (unless, forM_)
import           Data.Foldable (foldlM)

import           Control.Monad.Error (Error(..), MonadError(..), ErrorT)
import           Control.Monad.State (StateT)
import qualified Data.Set as Set

import           Kant.Name
import           Kant.Environment
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

class (MonadSubst m, MonadError TyCheckError m, Functor m, Applicative m) =>
      MonadTyCheck m
instance (Monad m, Functor m, Applicative m) =>
         MonadTyCheck (StateT Tag (ErrorT TyCheckError m))
instance (Monad m, Functor m, Applicative m) =>
         MonadTyCheck (ErrorT TyCheckError (StateT Tag m))

class TyCheck a where
    tyCheck :: MonadTyCheck m => Env -> a -> m Env

checkDup :: MonadTyCheck m => Id -> Maybe Env -> m Env
checkDup n Nothing    = throwError (DuplicateName (free n))
checkDup _ (Just env) = return env

instance (v ~ TName) => TyCheck (ModuleT v) where
    tyCheck env (Module decls') = foldlM tyCheck env decls'

instance (v ~ TName) => TyCheck (DeclT v) where
    -- TODO we are tychecking before verifying that there are no duplicates
    tyCheck env (Val n t) = do t' <- nf env t
                               ty <- tyCheckT env t'
                               checkDup n (addVal env (free n) ty t')
    tyCheck env (Postulate n ty) =
        do tyCheckT env ty
           checkDup n (addAbst env (free n) ty)
    tyCheck env (Data c dd@(Tele pars (DataT l cons))) =
        -- TODO finish
        addData env c dd (DuplicateName . free)

tyCheckT :: MonadTyCheck m => Env -> Term -> m Term
tyCheckT env (Var v) = maybe (throwError (OutOfBounds v)) return (envTy env v)
tyCheckT _   (Type l) = return (Type (l + 1))
-- TODO we manually have a "large" arrow here, but ideally we'd like to have
-- some kind of level polymorphism so that the arrow operator can be postulated
-- like any other.
tyCheckT env₁ (Arr (Abs ty₁ (Scope b ty₂))) =
    do tyty₁ <- tyCheckT env₁ ty₁
       tyty₁' <- nf env₁ tyty₁
       case tyty₁' of
           Type l₁ -> -- forget b ty₁ $
                      do let env₂ = upAbst env₁ b ty₁
                         tyty₂ <- tyCheckT env₂ ty₂
                         tyty₂' <- nf env₂ tyty₂
                         case tyty₂' of
                             Type l₂ -> return (Type (max l₁ l₂))
                             _       -> throwError (ExpectingType ty₂ tyty₂)
           _ -> throwError (ExpectingType ty₁ tyty₁)
tyCheckT env (App t₁ t₂) =
    do ty₁ <- tyCheckT env t₁
       ty₁' <- nf env ty₁
       case ty₁' of
           Arr (Abs ty₂ (Scope b ty₃)) -> do tyCheckEq env ty₂ t₂; subst b t₂ ty₃
           _                           -> throwError (ExpectingFunction t₁ ty₁)
tyCheckT env₁ (Lam (Abs ty (Scope b t))) =
    do tyty <- tyCheckT env₁ ty
       tyty' <- nf env₁ tyty
       case tyty' of
           Type _ -> -- forget b ty $
                     do let env₂ = upAbst env₁ b ty
                        tyt <- tyCheckT env₂ t
                        return (Arr (Abs ty (Scope b tyt)))
           _ -> throwError (ExpectingType ty tyty)
tyCheckT env (Constr c pars args) =
    tyCheckT env (app (Var (free c) : pars ++ args))
tyCheckT env₁ (Fix (Tele pars (Abs ty (Scope b t)))) =
     do let ty' = pis pars ty
        tyCheckT env₁ ty'
        let env₂ = foldr (\(v, tyv) e -> upAbst e v tyv) env₁ pars
            env₃ = upAbst env₂ b ty'
        tyCheckEq env₃ ty t
        return ty'
tyCheckT env ct@(Case t (Scope b ty) brs) =
    do tyt <- tyCheckT env t
       tyCheckT (upAbst env b tyt) ty
       tyt' <- nf env tyt
       case unrollApp tyt' of
           (Var (Plain tyc), args) ->
               case envData' env tyc of
                   Just (Tele pars (DataT _ cons)) | length pars == length args ->
                       if length brs /= Set.size (Set.fromList (map fst brs))
                       then throwError (WrongBranchNumber ct)
                       else do forM_ brs (checkBr (map fst pars) args cons)
                               subst b t ty
                   _ -> canon tyt
           _ -> canon tyt'
  where
    canon = throwError . ExpectingCanonical t
    checkBr typars args cons (c, Tele (branchBs -> bs) t') =
        case [dpars | ConstrT c' dpars <- cons, c == c'] of
            [] -> throwError (NotConstructor c ct)
            (dpars₁@(Tele (length -> i) Proxy) : _) | i == length bs ->
                do -- First, we substitute the type parameters with the actual
                   -- ones in the data parameters
                   Tele dpars₂ Proxy <- substBranch (branch typars dpars₁) args
                   -- Then, we substitute the parameters names with the names
                   -- given by the branch.  First we make sure that each
                   -- parameter has a name
                   return ()
                   -- bs' <- fillNames bs
                   -- let vs = zip (map fst parsd) [Var ta | Just ta <- bs']
                   -- -- Then we replace the references to data parameters
                   -- parsd₂ <- sequence [ (b',) <$> substManyB vs ty'
                   --                    | (b', ty') <- zip bs' parsd₁ ]
                   -- -- We put all the matched variables in the context
                   -- sequence [upAbst' b' ty' | (b', ty') <- parsd₂]
                   -- -- Finally, we replace the abstracted variable with the
                   -- -- refined variable
                   -- let ref = Constr c (map snd parsty) (map snd parsd₂)
                   -- (`tyCheckEq`  t') =<< substB b ref ty
                   -- -- and we remove the vars from the ctx
                   -- sequence [delCtx' b' | (b', _) <- parsd₂]
            _ -> throwError (WrongArity c ct)

-- | @tyCheckEq ty t@ thecks that the term @t@ has type @ty@.
tyCheckEq :: MonadTyCheck m => Env -> Term -> Term -> m ()
tyCheckEq env ty t =
    do ty' <- tyCheckT env t
       eqb <- eqCum env ty' ty
       unless eqb (throwError (Mismatch ty t ty'))

-- | @'eqCum' ty₁ ty₂@ checks if ty₁ is equal to ty₂, including cumulativity.
--   For example @'eqCum' ('Type' 1) ('Type' 4)@ will succeed, but @'eqCum'
--   ('Type' 4) ('Type' 1)@ will fail.
eqCum :: MonadTyCheck m => Env -> Term -> Term -> m Bool
eqCum env t₁ t₂ = do t₁' <- nf env t₁; t₂' <- nf env t₂
                     case (t₁', t₂') of
                         (Type l₁, Type l₂) -> return (l₁ <= l₂)
                         _                  -> eqSubst t₁' t₂'
