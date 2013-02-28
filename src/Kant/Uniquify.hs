module Kant.Uniquify
    ( slam ) where

import           Control.Monad (when, void)
import           Data.Maybe (fromMaybe)
import           Data.Traversable (mapM)
import           Prelude hiding (mapM)

import           Control.Monad.State (MonadState(..), evalState, execState, State)
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map

import           Kant.Term
import           Kant.Environment

uniquify :: (Ord v, Eq v) => Env v -> [Term v] -> [Term v]
uniquify env ts = evalState (mapM (mapM go) ts) (Map.fromList fs)
  where
    fs   = zip (Set.toList (execState (mapM (freeVars env) ts) Set.empty))
               (repeat (0 :: Integer))
    go v = do m <- get
              let ix = fromMaybe 0 (Map.lookup v m)
              put (Map.insert v (ix+1) m)
              return (if ix == 0 then v else envRename env v (++ show ix))

freeVars :: (Ord v) => Env v -> Term v -> State (Set v) ()
freeVars env t = void (mapM go t)
  where go v = when (envFree env v) (do s <- get; put (Set.insert v s))

slam :: Ord v => Env v -> [Term v] -> [TermId]
slam = undefined
