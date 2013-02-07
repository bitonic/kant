{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}
module Kant.TyCheck
    ( TyCheckError(..)
    , TyCheckM
    , TyCheck(..)
    , tyCheck'
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
import           Kant.Syntax

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
    tyCheck env (ValDecl val)   = tyCheck env val
    tyCheck env (Postulate n t) =
        case Env.envTy env n of
            Just _ -> throwError (DuplicateName n)
            _      -> addAbst env n t
    tyCheck env (DataDecl dat)  = tyCheck env dat

instance TyCheck Val where
    tyCheck env vd@(Val _ ty t) =
        do env' <- addVal env vd
           env' <$ tyCheckEq env' ty t

instance TyCheck Data where
    tyCheck env dd =
        do let ((c, ty), cons) = dataDecl dd
           tyCheck' env ty
           env' <- addAbst env c ty
           mapM_ (tyCheck' env') (map snd cons)
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

tyCheck' :: Ord a => EnvT a -> TermT a -> TyCheckM (TermT a)
tyCheck' env (Var v) = envTy env v
tyCheck' _ (Type l) = return (Type (l + 1))
-- TODO we manually have a "large" arrow here, but ideally we'd like to have
-- some kind of level polymorphism so that the arrow operator can be postulated
-- like any other.
tyCheck' env (arrV (envNest env) -> IsArr ty s) =
    do ty' <- tyCheck' env ty
       case nf env ty' of
           Type l₁ ->
               do let env' = nestEnv' env (const (Just ty))
                  tys <- tyCheck' env' (fromScope s)
                  case nf env' tys of
                      Type l₂ -> return (Type (max l₁ l₂))
                      _       -> expectingType env' (fromScope s) tys
           _ -> expectingType env ty ty'
tyCheck' env (App t₁ t₂) =
    do ty₁ <- tyCheck' env t₁
       case arrV (envNest env) (nf env ty₁) of
           IsArr ty₂ s -> instantiate1 t₂ s <$ tyCheckEq env ty₂ t₂
           NoArr _     -> expectingFunction env t₁ ty₁
tyCheck' env (Lam ty s) =
    do let ar = envNest env <$> arrow
       tyCheck' env ty
       tys <- toScope <$> nestTyCheckM env s (const ty) tyCheck'
       return (App (App ar ty) (Lam ty tys))
tyCheck' env ct@(Case t@(Var v) ty₁ brs) =
    do ty₂ <- tyCheck' env t
       -- Check if the scrutined's type is canonical, which amounts to checking
       -- that it is an application, we can find a matching type constructor,
       -- and the arguments are all there.
       case unrollApp ty₂ of
           (Var (envData' env -> Just (Data _ pars₁ _ cons)), args)
               | length pars₁ == length args ->
                   -- Check that the number of branches is just right
                   if length brs /= Set.size (Set.fromList [c | (c, _, _) <- brs])
                   then wrongBranchNumber env ct
                   else ty₁ <$ forM_ brs (checkBr cons ty₂)
           _ -> expectingCanonical env t ty₂
  where
    checkBr cons ty₂ br@(c, i, s) =
        -- Check that each constructor is indeed a constructor for our datatype
        case lookup c cons of
            Nothing -> notConstructor env br
            -- Check that the number of arguments given to the constructor are
            -- all there
            Just pars₂ | length pars₂ == i ->
                do let -- Get the new environment with the types for the newly
                       -- bound variables
                       env'   = prepareVars pars₂
                       -- Change the type of the scrutined to an application of
                       -- the constructor to the variables.
                       pars₂' = map B (zipWith Name (map fst pars₂) [0..])
                       env''  = caseRefine env' (F v) (F <$> ty₂)
                                           (app (map Var (envNest env' c : pars₂')))
                   tyCheckEq env'' (F <$> ty₁) (fromScope s)
            Just _ -> wrongArity env br
--    prepareVars :: [Param] -> EnvT (Var (Name Id Int) a)
    prepareVars = undefined

tyCheck' _ (Case _ _ _) =
    error "tyCheck' got a case with a non-variable, this should not happen"


-- | @tyCheckEq ty t@ thecks that the term @t@ has type @ty@.
tyCheckEq :: Ord a => EnvT a -> TermT a -> TermT a -> TyCheckM ()
tyCheckEq env ty t =
    do ty' <- tyCheck' env t
       unless (defeq env ty ty') (mismatch env ty t ty')

