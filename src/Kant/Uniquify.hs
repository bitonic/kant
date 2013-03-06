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

type FreshMonad v = State (Map v Id, Map Id Integer)

collectFree :: (Ord v) => Env v -> Term v -> FreshMonad v ()
collectFree env t = void (mapM go t)
  where
    go v = when (envFree env v) $
                do (names, ixs) <- get
                   let n = envPull env v
                       ixs' = case Map.lookup n ixs of
                                  Nothing -> Map.insert n 0 ixs
                                  Just _  -> ixs
                   put (Map.insert v n names, ixs')


collectRest :: (Ord v) => Env v -> Term v -> FreshMonad v ()
collectRest env t = void (mapM go t)
  where
    go v = do (names, ixs) <- get
              case Map.lookup v names of
                  Nothing -> let (n', ixs') = addVar (envPull env v) ixs
                             in  put (Map.insert v n' names, ixs')
                  Just _  -> return ()

addVar :: Id -> Map Id Integer -> (Id, Map Id Integer)
addVar n ixs =
    (n', Map.insert n (ix+1) ixs)
  where
    ix = fromMaybe 0 (Map.lookup n ixs)
    n' = n ++ show ix

freshVar :: Ord v => Env v -> v -> Id -> v
freshVar env v n = envRename env v (const n)

uniquify :: (Ord v, Show v) => Env v -> Term v -> FreshMonad v (Term v)
uniquify env t =
    do collectFree env t
       collectRest env t
       (names, ixs) <- get
       let t' = t >>= \v -> V (freshVar env v (names Map.! v))
       return (evalState (go t') ixs)
  where
    go t'@(V _) = return t'
    go Ty = return Ty
    go (Arr ty s) = Arr <$> go ty <*> goScope s
    go (Lam s) = Lam <$> goScope s
    go (App t₁ t₂) = App <$> go t₁ <*> go t₂
    go (Canon c ts') = Canon c <$> mapM go ts'
    go (Elim ce ts') = Elim ce <$> mapM go ts'
    go (Ann ty t') = Ann <$> go ty <*> go t'
    go t'@(Hole _) = return t'

    goScope :: (Ord v, Show v)
            => TermScope v -> State (Map Id Integer) (TermScope v)
    goScope s =
        case binding s of
            Nothing -> toScope <$> go (fromScope s)
            Just (Name n ()) ->
                do ixs <- get
                   let (n', ixs') = addVar n ixs
                       v' = B (Name n' ())
                   put ixs'
                   toScope <$> go (substitute v' (V v') (fromScope s))

slam :: (Ord v, Show v) => Env v -> Term v -> FreshMonad v TermId
slam env t = (envPull env <$>) <$> uniquify env t

slamVar :: (Ord v, Show v) => Env v -> v -> FreshMonad v (Maybe Id)
slamVar env v = do (names, _) <- get
                   return (envPull env . freshVar env v <$> Map.lookup v names)

runSlam :: FreshMonad v a -> a
runSlam s = evalState s (Map.empty, Map.empty)

slam' :: (Ord v, Show v) => Env v -> Term v -> TermId
slam' env t = runSlam (slam env t)
