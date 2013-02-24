{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Kant.TyCheck
    -- ( TyCheckError(..)
    -- , TyCheckM
    -- , TyCheck(..)
    -- , tyCheckT
    -- )
    where

import           Control.Applicative ((<$), (<$>))
import           Control.Monad (unless, forM_)

import           Control.Monad.Error (Error(..), MonadError(..))
import           Control.Monad.State (MonadState(..))
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

type TyCheckM = EnvM (Either TyCheckError)

-- class TyCheck a where
--     tyCheck :: Env -> a -> TyCheckM Env

-- instance (v ~ Tag) => TyCheck (ModuleT v) where
--     tyCheck env' (Module decls') = go decls' env'
--       where
--         go []             env = Right env
--         go (decl : decls) env = tyCheck env decl >>= go decls

-- instance (v ~ Tag) => TyCheck (DeclT v) where
--     tyCheck env (DataD dat)      = tyCheck env dat
--     tyCheck env (Val n t)        = do ty <- tyCheckT env t; addVal env n ty t
--     tyCheck env (Postulate n ty) = do tyCheckT env ty; addAbst env n ty

-- instance (v ~ Tag) => TyCheck (DataT v) where
--     tyCheck env dd@(Data tyc _ _ cons) =
--         do env₁ <- addData env dd
--            -- We assert that the type constructor is present
--            let Just ty = Env.envTy env₁ (Free tyc)
--            tyCheckT env ty
--            env' <- addAbst env tyc ty
--            forM_ cons $ \(c, _) -> do let Just ty' = Env.envTy env₁ (Free c)
--                                       tyCheckT env' ty'
--            return env₁

-- dupMaybe :: Id -> Maybe b -> TyCheckM b
-- dupMaybe _ (Just x) = return x
-- dupMaybe n Nothing  = throwError (DuplicateName n)

-- addAbst :: Env -> Id -> Term -> TyCheckM Env
-- addAbst env n t = dupMaybe n (Env.addAbst env n t)

-- addVal :: Env -> Id -> Term -> Term -> TyCheckM Env
-- addVal env n ty t = dupMaybe n (Env.addVal env n ty t)

-- addData :: Env -> Data -> TyCheckM Env
-- addData env dd = either (throwError . DuplicateName) return (Env.addData env dd)

-- envTy :: Env -> TName -> TyCheckM Term
-- envTy env v = maybe (throwError (OutOfBounds v)) return (Env.envTy env v)

forget :: MonadState s m => m b -> m b
forget m = do s <- get; x <- m; put s; return x

envTy :: Tag -> TyCheckM Term
envTy v = maybe (throwError (OutOfBounds v)) return =<< Env.envTy v

tyCheckT :: Term -> TyCheckM Term
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
    checkBr :: [(TBinder, Term)] -> [Constr] -> (ConId, Branch) -> TyCheckM ()
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
fillNames :: [TBinder] -> TyCheckM [TBinder]
fillNames [] = return []
fillNames (b@(Bind _ _) : bs) = (b :) <$> fillNames bs
fillNames (Wild : bs) =
    do v <- freshTag; (Bind "_" v :) <$> fillNames bs

-- | @tyCheckEq ty t@ thecks that the term @t@ has type @ty@.
tyCheckEq :: Term -> Term -> TyCheckM ()
tyCheckEq ty t =
    do ty' <- tyCheckT t
       eqb <- eqCum ty' ty
       unless eqb (throwError (Mismatch ty t ty'))

-- | @'eqCum' ty₁ ty₂@ checks if ty₁ is equal to ty₂, including cumulativity.
--   For example @'eqCum' ('Type' 1) ('Type' 4)@ will succeed, but @'eqCum'
--   ('Type' 4) ('Type' 1)@ will fail.
eqCum :: Term -> Term -> TyCheckM Bool
eqCum t₁ t₂ = do t₁' <- nf t₁; t₂' <- nf t₂
                 return $ case (t₁', t₂') of
                              (Type l₁, Type l₂) -> l₁ <= l₂
                              _                  -> t₁' == t₂'
