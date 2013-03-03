module Kant.Uniquify (slam, slam') where

import           Control.Applicative ((<$>), (<*>))
import           Control.Monad (when, void)
import           Data.Maybe (fromMaybe)
import           Data.Traversable (mapM)
import           Prelude hiding (mapM)

import           Control.Monad.State (MonadState(..), evalState, execState, State)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set

import           Bound
import           Bound.Name

import           Kant.Env
import           Kant.Term

uniquify :: (Ord v, Show v) => Env v -> [Term v] -> [Term v]
uniquify env ts = evalState (mapM go ts) (Map.fromList fs)
  where
    fs = zip (Set.toList (execState (mapM (freeVars env) ts) Set.empty))
             (repeat (0::Integer))

    go (V v) = return (V v)
    go Ty = return Ty
    go (Arr ty s) = Arr <$> go ty <*> goScope s
    go (Lam s) = Lam <$> goScope s
    go (App t₁ t₂) = App <$> go t₁ <*> go t₂
    go (Canon c ts') = Canon c <$> mapM go ts'
    go (Elim ce ts') = Elim ce <$> mapM go ts'
    go (Ann ty t) = Ann <$> go ty <*> go t

    goScope :: (Ord v, Show v) => TermScope v -> State (Map Id Integer) (TermScope v)
    goScope s =
        case binding s of
            Nothing -> toScope <$> go (fromScope s)
            Just (Name n ()) ->
                do m <- get
                   let ix = fromMaybe 0 (Map.lookup n m)
                       v' = B (Name (if ix == 0 then n else n ++ show ix) ())
                   put (Map.insert n (ix+1) m)
                   toScope <$> go (substitute v' (V v') (fromScope s))

freeVars :: (Ord v) => Env v -> Term v -> State (Set Id) ()
freeVars env t = void (mapM go t)
  where go v = when (envFree env v) (do s <- get; put (Set.insert (envPull env v) s))

slam :: (Ord v, Show v) => Env v -> [Term v] -> [TermId]
slam env ts = map (envPull env <$>) (uniquify env ts)

slam' :: (Ord v, Show v) => Env v -> Term v -> TermId
slam' env t = head (slam env [t])
