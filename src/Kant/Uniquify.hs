module Kant.Uniquify
    ( runFresh
    , slamVar
    , slam
    , slam'
    , formHole
    ) where

import           Control.Applicative ((<$>), (<*>))
import           Control.Monad (when, void)
import           Data.Maybe (fromMaybe)
import           Data.Traversable (mapM)
import           Prelude hiding (mapM)

import           Control.Monad.State (MonadState(..), evalState, State)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import           Bound
import           Bound.Name

import           Kant.Env
import           Kant.Term

type FreshMonad v = State (Map v Id, Map Id Integer)

collectFree :: (Ord v, Show v) => Env v -> Term v -> FreshMonad v ()
collectFree env t = void (mapM go t)
  where go v = when (envFree env v) (addVar env v)

addVar :: (Ord v, Show v) => Env v -> v -> FreshMonad v ()
addVar env v =
    do (names, ixs) <- get
       case Map.lookup v names of
           Nothing -> let (n', ixs') = addVar' (envPull env v) ixs
                      in  put (Map.insert v n' names, ixs')
           Just _  -> return ()

addVar' :: Id -> Map Id Integer -> (Id, Map Id Integer)
addVar' n ixs = (n', Map.insert n (ix+1) ixs)
  where
    ix = fromMaybe 0 (Map.lookup n ixs)
    n' = n ++ show ix

freshVar :: (Ord v, Show v) => Env v -> v -> Map v Id -> v
freshVar env v names = envRename env v (const (names Map.! v))

uniquify :: (Ord v, Show v) => Env v -> Term v -> FreshMonad v (Term v)
uniquify env t =
    do collectFree env t
--       mapM (addVar env) t
       (names, ixs) <- get
       let t' = t >>= \v -> V (freshVar env v names)
       return t'
--       return (evalState (go t') ixs)
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
                   let (n', ixs') = addVar' n ixs
                       v' = B (Name n' ())
                   put ixs'
                   toScope <$> go (substitute v' (V v') (fromScope s))

slam :: (Ord v, Show v) => Env v -> Term v -> FreshMonad v TermId
slam env t = (envPull env <$>) <$> uniquify env t

slamVar :: (Ord v, Show v) => Env v -> v -> FreshMonad v Id
slamVar env v = do addVar env v
                   (names, _) <- get
                   return (envPull env (freshVar env v names))

runFresh :: FreshMonad v a -> a
runFresh s = evalState s (Map.empty, Map.empty)

slam' :: (Ord v, Show v) => Env v -> Term v -> TermId
slam' env t = runFresh (slam env t)

formHole :: (Show v, Ord v) => Env v -> HoleId -> Term v -> FreshMonad v HoleCtx
formHole env hn ty =
    do mapM (addVar env) pruned
       hctx <- Map.fromList <$>
               sequence [ (,) <$> slamVar env v <*> slam env (getTy (envType env v))
                        | v <- pruned]
       ty' <- slam env ty
       return HoleCtx{holeName = hn, holeGoal = ty', holeCtx = hctx}
  where
    pruned = prune (envVars env) Set.empty

    prune []       _  = []
    prune (v : vs) ns = let vn = envPull env v
                        in if Set.member vn ns || envFree env v
                           then prune vs ns
                           else v : prune vs (Set.insert vn ns)

    getTy (Just ty') = ty'
    getTy _          = error "formHole: var with no type in context"
