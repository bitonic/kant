{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Kant.TyCheck
    ( TyCheckError(..)
    , TyCheckM
    , TyCheck(..)
    , tyCheckT
    ) where

import           Control.Applicative ((<$))
import           Control.Arrow (first)
import           Control.Monad (unless, forM_)

import           Control.Monad.Error (Error(..), MonadError(..))
import qualified Data.Set as Set

import           Kant.Term
import qualified Kant.Environment as Env
import           Kant.Environment hiding (envTy, addAbst, addVal, addData)
import           Kant.Reduce

data TyCheckError
    = TyCheckError
    | OutOfBounds TName
    | DuplicateName Id
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

type TyCheckM = Either TyCheckError

class TyCheck a where
    tyCheck :: Env -> a -> TyCheckM Env

instance (f ~ Id, t ~ Tag) => TyCheck (ModuleT f t) where
    tyCheck env' (Module decls') = go decls' env'
      where
        go []             env = Right env
        go (decl : decls) env = tyCheck env decl >>= go decls

instance (f ~ Id, t ~ Tag) => TyCheck (DeclT f t) where
    tyCheck env (DataD dat)      = tyCheck env dat
    tyCheck env (Val n t)        = do ty <- tyCheckT env t; addVal env n ty t
    tyCheck env (Postulate n ty) = do tyCheckT env ty; addAbst env n ty

instance (f ~ Id, t ~ Tag) => TyCheck (DataT f t) where
    tyCheck env dd@(Data tyc _ _ cons) =
        do env₁ <- addData env dd
           -- We assert that the type constructor is present
           let Just ty = Env.envTy env₁ (Free tyc)
           tyCheckT env ty
           env' <- addAbst env tyc ty
           forM_ cons $ \(c, _) -> do let Just ty' = Env.envTy env₁ (Free c)
                                      tyCheckT env' ty'
           return env₁

dupMaybe :: Id -> Maybe b -> TyCheckM b
dupMaybe _ (Just x) = return x
dupMaybe n Nothing  = throwError (DuplicateName n)

addAbst :: Env -> Id -> Term -> TyCheckM Env
addAbst env n t = dupMaybe n (Env.addAbst env n t)

addVal :: Env -> Id -> Term -> Term -> TyCheckM Env
addVal env n ty t = dupMaybe n (Env.addVal env n ty t)

addData :: Env -> Data -> TyCheckM Env
addData env dd = either (throwError . DuplicateName) return (Env.addData env dd)

envTy :: Env -> TName -> TyCheckM Term
envTy env v = maybe (throwError (OutOfBounds v)) return (Env.envTy env v)

tyCheckT :: Env -> Term -> TyCheckM Term
tyCheckT env (Var v) = envTy env v
tyCheckT _ (Type l) = return (Type (l + 1))
-- TODO we manually have a "large" arrow here, but ideally we'd like to have
-- some kind of level polymorphism so that the arrow operator can be postulated
-- like any other.
tyCheckT env (Arr b ty₁ ty₂) =
    do tyty₁ <- tyCheckT env ty₁
       case nf env tyty₁ of
           Type l₁ ->
               do let env' = upAbst' env b ty₁
                  tyty₂ <- tyCheckT env' ty₂
                  case nf env' tyty₂ of
                      Type l₂ -> return (Type (max l₁ l₂))
                      _       -> throwError (ExpectingType ty₂ tyty₂)
           _ -> throwError (ExpectingType ty₁ tyty₁)
tyCheckT env (App t₁ t₂) =
    do ty₁ <- tyCheckT env t₁
       case nf env ty₁ of
           Arr b ty₂ ty₃ -> subst' b t₁ ty₃ <$ tyCheckEq env ty₂ t₂
           _             -> throwError (ExpectingFunction t₁ ty₁)
tyCheckT env (Lam b ty t) =
    do tyty <- tyCheckT env ty
       case nf env tyty of
           Type _ -> do tyt <- tyCheckT (upAbst' env b ty) t
                        return (Arr b ty tyt)
           _ -> throwError (ExpectingType ty tyty)
tyCheckT env (Constr c pars args) =
    tyCheckT env (app (free c : pars ++ args))
tyCheckT env (Fix b pars ty t) =
     do let ty' = (arrs pars ty)
        tyCheckT env ty'
        return ty'
tyCheckT env ct@(Case b t ty brs) =
    do tyt <- tyCheckT env t
       tyCheckT (upAbst' env b tyt) ty
       case unrollApp tyt of
           (Var (envData' env -> Just (Data _ pars _ cons)), args)
               | length pars == length args ->
                   -- Check that the number of branches is just right
                   if length brs /= Set.size (Set.fromList [c | (c, _, _) <- brs])
                   then throwError (WrongBranchNumber ct)
                   else subst' b t ty <$
                        forM_ brs (checkBr tyt (zip (map fst pars) args) cons)
           _ -> throwError (ExpectingCanonical t tyt)
  where
    checkBr :: Term -> [Param] -> [Constr] -> Branch -> TyCheckM ()
    checkBr tyt parsty cons (c, bs, t') =
        -- Check that the constructor is indeed a constructor for our datatype
        case lookup c cons of
            Nothing -> throwError (NotConstructor c ct)
            -- Check that the number of arguments given to the constructor are
            -- all there
            Just parsd | length parsd == length bs ->
                do let -- First, we substitute the type parameters with the
                       -- actual ones in the data parameters
                       parsd₁ = [substMany parsty ty' | (_, ty') <- parsd]
                       -- Then, we substitute the parameters names with the
                       -- names given by the branch.  First we make sure that
                       -- each parameter has a name
                       (bs', env₁) = fillNames env bs
                       vs = zip (map fst parsd) [bound ta | Bind _ ta <- bs']
                       -- Then we replace the references to data parameters
                       parsd₂ = [(b', substMany vs ty') | (b', ty') <- zip bs' parsd₁]
                       -- We put all the matched variables in the context
                       env₂ = foldr (\(b', ty') e -> upAbst' e b' ty') env₁ parsd₂
                       -- Finally, we replace the abstracted variable with the
                       -- refined variable
                       env₃ = upVal' env₂ b tyt
                                     (Constr c (map snd parsty) (map snd parsd₂))
                   tyCheckEq env₃ ty t'
            _ -> throwError (WrongArity c ct)

-- TODO I don't think it's safe to generate names here considering that then we
-- throw away the Env.
fillNames :: Env -> [TBinder] -> ([TBinder], Env)
fillNames env [] = ([], env)
fillNames env (b@(Bind _ _) : bs) = first (b :) (fillNames env bs)
fillNames env (Wild : bs) = first (Bind "_" (toTag c) :) (fillNames env' bs)
  where (c, env') = bumpCount env

-- | @tyCheckEq ty t@ thecks that the term @t@ has type @ty@.
tyCheckEq :: Env -> Term -> Term -> TyCheckM ()
tyCheckEq env ty t =
    do ty' <- tyCheckT env t
       unless (eqCum env ty' ty) (throwError (Mismatch ty t ty'))

-- | @'eqCum' ty₁ ty₂@ checks if ty₁ is equal to ty₂, including cumulativity.
--   For example @'eqCum' ('Type' 1) ('Type' 4)@ will succeed, but @'eqCum'
--   ('Type' 4) ('Type' 1)@ will fail.
eqCum :: Env -> Term -> Term -> Bool
eqCum env (nf env -> Type l₁) (nf env -> Type l₂) = l₁ <= l₂
eqCum env (nf env -> ty₁)     (nf env -> ty₂)     = ty₁ == ty₂
