{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Kant.TyCheck
    ( TyCheckError(..)
    , TyCheckM
    , TyCheck(..)
    , tyCheckT
    ) where

import           Control.Applicative ((<$>), (<$))
import           Control.Arrow ((***))
import           Control.Monad (unless, forM_)
import           Prelude hiding ((!!), length, splitAt)

import           Control.Monad.Error (Error(..), MonadError(..))
import qualified Data.Set as Set

import           Bound
import           Bound.Name
import           Numeric.Natural

import           Kant.Common
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
    | NotConstructor Id Term
    | WrongArity Id Term
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

notConstructor, wrongArity :: Ord a => EnvT a -> Id -> TermT a -> TyCheckM b
notConstructor env c t = throwError (NotConstructor c (pullTerm env t))
wrongArity env c t = throwError (WrongArity c (pullTerm env t))

instance Error TyCheckError where
    noMsg = TyCheckError

type TyCheckM = Either TyCheckError

nestTyCheckM :: EnvT a
             -> TScope a
             -> TermT a
             -> (EnvT (Var (TName ()) a) -> TermT (Var (TName ()) a) -> TyCheckM c)
             -> TyCheckM c
nestTyCheckM env s ty f = f (nestEnv' env (Just . const ty)) (fromScope s)

class TyCheck a where
    tyCheck :: Env -> a -> TyCheckM Env

instance TyCheck Module where
    tyCheck env' (Module decls') = go decls' env'
      where
        go []             env = Right env
        go (decl : decls) env = tyCheck env decl >>= go decls

instance TyCheck Decl where
    tyCheck env (DataD dat)      = tyCheck env dat
    tyCheck env (Val n t)        = do ty <- tyCheckT env t; addVal env n ty t
    tyCheck env (Postulate n ty) = do tyCheckT env ty; addAbst env n ty

instance TyCheck Data where
    tyCheck env dd = do let ((c, (ty, _)), cons) = dataDecl dd
                        tyCheckT env ty
                        env' <- addAbst env c ty
                        mapM_ (tyCheckT env') (map (\(_, (ty', _)) -> ty') cons)
                        addData env dd

dupMaybe :: Id -> Maybe b -> TyCheckM b
dupMaybe _ (Just x) = return x
dupMaybe n Nothing  = throwError (DuplicateName n)

addAbst :: Env -> Id -> Term -> TyCheckM Env
addAbst env n t = dupMaybe n (Env.addAbst env n t)

addVal :: Env -> Id -> Term -> Term -> TyCheckM Env
addVal env n ty t = dupMaybe n (Env.addVal env n ty t)

addData :: Env -> Data -> TyCheckM Env
addData env dd = either (throwError . DuplicateName) return (Env.addData env dd)

envTy :: Eq a => EnvT a -> a -> TyCheckM (TermT a)
envTy env v = maybe (outOfBounds env v) return (Env.envTy env v)

tyCheckT :: forall a. (Ord a, Show a) => EnvT a -> TermT a -> TyCheckM (TermT a)
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
       tys <- toScope <$> nestTyCheckM env s ty tyCheckT
       return (Arr ty tys)
tyCheckT env@Env{envNest = nest} (Constr c pars args) =
    tyCheckT env (app (Var (nest c) : pars ++ args))
tyCheckT env (Fix ty (FixT i ss)) =
     do tyCheckT env ty
        return ty
tyCheckT env@Env{envNest = nest} ct@(Case t (CaseT s brs)) =
    do ty <- tyCheckT env t
       -- Check if the scrutined's type is canonical, which amounts to checking
       -- that it is an application, we can find a matching type constructor,
       -- and the arguments are all there.
       case unrollApp ty of
           (Var (envData' env -> Just (Data _ pars _ cons)), args)
               | length pars == length args ->
                   -- Check that the number of branches is just right
                   if length brs /=
                      fi (Set.size (Set.fromList [c | BranchT c _ _ <- brs]))
                   then wrongBranchNumber env ct
                   else instantiate1 t s <$ forM_ brs (checkBr args cons s)
           _ -> expectingCanonical env t ty
  where
    -- TODO this is quite messy. The main culprit is the type-silent invariant
    -- that all the lists are of the same length, and thus all the unsafe
    -- indexing. It would be nice to have it to be safer and more "obviously
    -- correct".
    checkBr :: [TermT a] -> [Constr] -> TScope a -> BranchT TermT a -> TyCheckM ()
    checkBr args cons tys (BranchT c i ss) =
        -- Check that each constructor is indeed a constructor for our datatype
        case [con | con@(ConstrT c' _) <- cons, c == c'] of
            [] -> notConstructor env c ct
            -- Check that the number of arguments given to the constructor are
            -- all there
            (ConstrT _ pars : _) | length pars == i ->
                do let -- Get the new environment with the types for the bound
                       -- variables.  Note that we replace the scoped arguments
                       -- to the type constructors with what we actually have.
                       env' = intVars env
                              (map (nest *** (instantiateList args . fmap nest)) pars)
                       -- Prepare the term for this branch
                       cont = Constr c (map (fmap F) args)
                              (map (Var . B) (zipWith Name (map fst pars) [0..]))
                       -- The type that we'd expect for the body
                       ty' = instantiate1 cont (F <$> tys)
                       -- Remove the branch scope's inner scope
                       s' = toScope (instantiate1 cont (fromScope ss))
                   tyCheckEq env' ty' (fromScope s')
            _ -> wrongArity env c ct

-- | Prepares an environment with where variable `n' has type `pars !! n', and
--   all the references to previous elements in `pars' are int variables as
--   well.
intVars :: (Eq a) => EnvT a -> [(a, TermT a)] -> EnvT (Var (TName Natural) a)
intVars env@Env{envPull = pull} pars =
    let -- First, bring all the types of the parameters of the data
        -- constructor to the right level of boundness
        nested₁ = [(n, F <$> t) | (n, t) <- pars]
        -- Then the tricky part: for each parameter of the data
        -- constructor, replace the variables that represent previous
        -- arguments with the variables that will represent them in the
        -- current scope.
        nested₂ = [ foldr (\(n, j) t -> substitute (F n) (Var (B (Name (pull n) j))) t)
                          (snd (nested₁ !! i))
                          (zip (map fst nested₁) (if i == 0 then [] else [0..(i-1)]))
                  | i <- [0..(length nested₁ - 1)] ]
    in nestEnv env (\i -> Just (nested₂ !! i))

-- | @tyCheckEq ty t@ thecks that the term @t@ has type @ty@.
tyCheckEq :: (Ord a, Show a) => EnvT a -> TermT a -> TermT a -> TyCheckM ()
tyCheckEq env ty t =
    do ty' <- tyCheckT env t
       unless (eqCum env ty' ty) (mismatch env ty t ty')

-- | @'eqCum' ty₁ ty₂@ checks if ty₁ is equal to ty₂, including cumulativity.
--   For example @'eqCum' ('Type' 1) ('Type' 4)@ will succeed, but @'eqCum'
--   ('Type' 4) ('Type' 1)@ will fail.
eqCum :: (Ord a, Show a) => EnvT a -> TermT a -> TermT a -> Bool
eqCum env (nf env -> Type l₁) (nf env -> Type l₂) = l₁ <= l₂
eqCum env (nf env -> ty₁)     (nf env -> ty₂)     = ty₁ == ty₂
