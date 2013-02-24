{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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

import           Kant.Environment hiding (envTy)
import qualified Kant.Environment as Env
import           Kant.Reduce
import           Kant.Term

data TyCheckError
    = TyCheckError
    | OutOfBounds Tag
    | DuplicateName Tag
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
                  unless b (throwError (DuplicateName (toTag n)))

instance (v ~ Tag) => TyCheck (ModuleT v) where
    tyCheck (Module decls') = mapM_ tyCheck decls'

instance (v ~ Tag) => TyCheck (DeclT v) where
    -- TODO we are tychecking before verifying that there are no duplicates
    tyCheck (Val n t) = do ty <- tyCheckT t; checkDup n (addVal (toTag n) ty t)
    tyCheck (Postulate n ty) = do tyCheckT ty; checkDup n (addAbst (toTag n) ty)
    tyCheck (Data c dd@(Tele pars (DataT l cons))) =
        -- TODO finish
        addData c dd (DuplicateName . toTag)

forget :: MonadState s m => m b -> m b
forget m = do s <- get; x <- m; put s; return x

envTy :: MonadTyCheck m => Tag -> m Term
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
           Type l₁ -> forget $
                      do upAbst' b ty₁
                         tyty₂ <- tyCheckT ty₂
                         tyty₂' <- nf tyty₂
                         case tyty₂' of
                             Type l₂ -> return (Type (max l₁ l₂))
                             _       -> throwError (ExpectingType ty₂ tyty₂)
           _ -> throwError (ExpectingType ty₁ tyty₁)
tyCheckT (App t₁ t₂) =
    do ty₁ <- tyCheckT t₁
       ty₁' <- nf ty₁
       case ty₁' of
           Arr ty₂ (Scope b ty₃) -> substB b t₂ ty₃ <$ tyCheckEq ty₂ t₂
           _                     -> throwError (ExpectingFunction t₁ ty₁)
tyCheckT (Lam ty (Scope b t)) =
    do tyty <- tyCheckT ty
       tyty' <- nf tyty
       case tyty' of
           Type _ -> forget $ do upAbst' b ty
                                 tyt <- tyCheckT t
                                 return (Arr ty (Scope b tyt))
           _ -> throwError (ExpectingType ty tyty)
tyCheckT (Constr c pars args) =
    tyCheckT (app (Var (toTag c) : pars ++ args))
tyCheckT (Fix (Tele pars (FixT ty (Scope b t)))) =
    -- TODO finish
     do let ty' = arrs pars ty
        tyCheckT ty'
        return ty'
tyCheckT ct@(Case t (Scope b ty) brs) =
    do tyt <- tyCheckT t
       forget $ do upAbst' b tyt; tyCheckT ty
       tyt' <- nf tyt
       case unrollApp tyt' of
           (Var tyc, args) ->
               do dd <- envData' (toId tyc)
                  case dd of
                      Just (Tele pars (DataT _ cons)) | length pars == length args ->
                          if length brs /= Set.size (Set.fromList (map fst brs))
                          then throwError (WrongBranchNumber ct)
                          else substB b t ty <$
                               forM_ brs (forget .
                                          checkBr (zip (map fst pars) args) cons)
                      _ -> canon tyt
           _ -> canon tyt'
  where
    canon = throwError . ExpectingCanonical t
    checkBr parsty cons (c, Branch bs t') =
        case [parsd | ConstrT c' (Tele parsd Proxy) <- cons, c == c'] of
            [] -> throwError (NotConstructor c ct)
            (parsd:_) | length parsd == length bs ->
                do -- First, we substitute the type parameters with the actual
                   -- ones in the data parameters
                   let parsd₁ = [substManyB parsty ty' | (_, ty') <- parsd]
                   -- Then, we substitute the parameters names with the names
                   -- given by the branch.  First we make sure that each
                   -- parameter has a name
                   bs' <- fillNames bs
                   let vs = zip (map fst parsd) [Var ta | Bind _ ta <- bs']
                   -- Then we replace the references to data parameters
                       parsd₂ = [ (b', substManyB vs ty')
                                | (b', ty') <- zip bs' parsd₁ ]
                   -- We put all the matched variables in the context
                   sequence [upAbst' b' ty' | (b', ty') <- parsd₂]
                   -- Finally, we replace the abstracted variable with the
                   -- refined variable
                   let ref = Constr c (map snd parsty) (map snd parsd₂)
                   tyCheckEq (substB b ref ty)  t'
            _ -> throwError (WrongArity c ct)

-- TODO I don't think it's safe to generate names here considering that then we
-- throw away the Env.
fillNames :: MonadTyCheck m => [TBinder] -> m [TBinder]
fillNames [] = return []
fillNames (b@(Bind _ _) : bs) = (b :) <$> fillNames bs
fillNames (Wild : bs) =
    do v <- freshTag; (Bind "_" v :) <$> fillNames bs

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
