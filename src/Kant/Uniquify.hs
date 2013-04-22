module Kant.Uniquify
    ( runFresh
    , slamVar
    , slam
    , slam'
    , formHole
    ) where

import           Control.Monad (when, void)
import           Data.Maybe (fromMaybe)
import           Data.Traversable (mapM)
import           Prelude hiding (mapM)

import           Control.Monad.State (MonadState(..), evalState, State)
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap

import           Bound
import           Bound.Name

import           Kant.Common
import           Kant.Env
import           Kant.Term

type FreshMonad v = State (HashMap v Id, HashMap Id Integer)

collectFree :: VarC v => Env v -> Term r v -> FreshMonad v ()
collectFree env t = void (mapM go t)
  where go v = when (envFree env v) (addVar env v)

addVar :: VarC v => Env v -> v -> FreshMonad v ()
addVar env v =
    do (names, ixs) <- get
       case HashMap.lookup v names of
           Nothing -> let (n', ixs') = addVar' (envPull env v) ixs
                      in  put (HashMap.insert v n' names, ixs')
           Just _  -> return ()

addVar' :: Id -> HashMap Id Integer -> (Id, HashMap Id Integer)
addVar' n ixs = (n', HashMap.insert n (ix+1) ixs)
  where
    ix = fromMaybe 0 (HashMap.lookup n ixs)
    n' = n ++ if ix /= 0 then show ix else ""

freshVar :: VarC v => Env v -> v -> HashMap v Id -> v
freshVar env v names = envRename env v (const (names HashMap.! v))

uniquify :: VarC v => Env v -> Term r v -> FreshMonad v (Term r v)
uniquify env t =
    do collectFree env t
       mapM (addVar env) t
       (names, ixs) <- get
       let t' = t >>= \v -> V (freshVar env v names)
       return (evalState (go t') ixs)
  where
    go t'@(V _) = return t'
    go (Ty r) = return (Ty r)
    go (Arr ty s) = Arr <$> go ty <*> goScope s
    go (Lam s) = Lam <$> goScope s
    go (App t₁ t₂) = App <$> go t₁ <*> go t₂
    go (Canon c ts') = Canon c <$> mapM go ts'
    go (Elim ce ts') = Elim ce <$> mapM go ts'
    go (Ann ty t') = Ann <$> go ty <*> go t'
    go (Hole hn ts) = Hole hn <$> mapM go ts

    goScope :: VarC v => TermScope r v -> State (HashMap Id Integer) (TermScope r v)
    goScope s =
        case binding s of
            Nothing -> toScope <$> go (fromScope s)
            Just (Name n ()) ->
                do ixs <- get
                   let (n', ixs') = addVar' n ixs
                       v' = B (Name n' ())
                   put ixs' *> (toScope <$> go (substitute v' (V v') (fromScope s)))
                            <* put ixs

slam :: VarC v => Env v -> Term r v -> FreshMonad v (TermId r)
slam env t = (envPull env <$>) <$> uniquify env t

slamVar :: VarC v => Env v -> v -> FreshMonad v Id
slamVar env v = do addVar env v
                   (names, _) <- get
                   return (envPull env (freshVar env v names))

runFresh :: FreshMonad v a -> a
runFresh s = evalState s (HashMap.empty, HashMap.empty)

slam' :: VarC v => Env v -> Term r v -> TermId r
slam' env t = runFresh (slam env t)

formHole :: VarC v
         => Env v -> HoleId -> TermRef v -> [(TermRef v, TermRef v)]
         -> FreshMonad v (HoleCtx)
formHole env hn goal ts =
    do hctx <- sequence [(,) <$> slam env t <*> slam env ty | (t, ty) <- ts]
       goal' <- slam env goal
       return HoleCtx{holeName = hn, holeGoal = goal', holeCtx = hctx}
