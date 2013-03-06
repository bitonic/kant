module Kant.Uniquify (runSlam, slamVar, slam, slam') where

import           Control.Applicative ((<$>), (<*>))
import           Control.Monad (when, void)
import           Data.Maybe (fromMaybe)
import           Data.Traversable (mapM)
import           Prelude hiding (mapM)

import           Control.Monad.State (MonadState(..), evalState, State)
import           Data.Map (Map)
import qualified Data.Map as Map

import           Bound
import           Bound.Name

import           Kant.Env
import           Kant.Term

type FreshMonad = State (Map Id Integer)

uniquify :: (Ord v, Show v) => Env v -> Term v -> FreshMonad (Term v)
uniquify env t = do freeVars env t; go t
  where
    go (V v) = return (V v)
    go Ty = return Ty
    go (Arr ty s) = Arr <$> go ty <*> goScope s
    go (Lam s) = Lam <$> goScope s
    go (App t₁ t₂) = App <$> go t₁ <*> go t₂
    go (Canon c ts') = Canon c <$> mapM go ts'
    go (Elim ce ts') = Elim ce <$> mapM go ts'
    go (Ann ty t') = Ann <$> go ty <*> go t'

    goScope :: (Ord v, Show v) => TermScope v -> FreshMonad (TermScope v)
    goScope s =
        case binding s of
            Nothing -> toScope <$> go (fromScope s)
            Just (Name n ()) ->
                do m <- get
                   let ix = fromMaybe 0 (Map.lookup n m)
                       v' = B (Name (if ix == 0 then n else n ++ show ix) ())
                   put (Map.insert n (ix+1) m)
                   toScope <$> go (substitute v' (V v') (fromScope s))

freeVars :: (Ord v) => Env v -> Term v -> FreshMonad ()
freeVars env t = void (mapM go t)
  where go v = when (envFree env v)
                    (do m <- get; put (Map.insert (envPull env v) 0 m))

slam :: (Ord v, Show v) => Env v -> Term v -> FreshMonad TermId
slam env t = (envPull env <$>) <$> uniquify env t

slamVar :: (Ord v, Show v) => Env v -> v -> FreshMonad v
slamVar env v =
    do m <- get
       let n = envPull env v
       return $ case Map.lookup n m of
                    Nothing -> v
                    Just i  -> envRename env v (++ show i)

runSlam :: FreshMonad a -> a
runSlam s = evalState s Map.empty

slam' :: (Ord v, Show v) => Env v -> Term v -> TermId
slam' env t = runSlam (slam env t)

