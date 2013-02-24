module Kant.Uniquify
    ( uniquify
    , revert
    ) where

import           Control.Applicative ((<$>))
import           Control.Monad (liftM)
import           Data.Maybe (fromMaybe)

import           Control.Monad.State (State, MonadState(..), evalState)
import           Data.Map (Map)
import qualified Data.Map as Map

import           Kant.Term
import           Kant.Environment

uniquify :: (Functor f, Subst f, MonadEnv m) => f Id -> m (f Tag)
uniquify t =
    fmap toTag `liftM`
    subst Var
          (\b f -> case b of
                       Wild -> return (Wild, f)
                       Bind n v₁ ->
                           do v₂ <- freshId
                              return (Bind n v₂,
                                      \v₃ -> if v₃ == v₁ then Var v₂ else f v₃))
          t

revert :: (Functor f, Subst f) => f Tag -> f Id
revert t = evalState (revert' (toId <$> t)) Map.empty

showIx :: Id -> Count -> Id
showIx v n = v ++ show n

revert' :: (Subst f) => f Id -> State (Map Id Count) (f Id)
revert' =
    subst Var
    (\b f -> case b of
                 Wild -> return (Wild, f)
                 Bind n v₁ ->
                     do ixs <- get
                        let ix = fromMaybe 0 (Map.lookup n ixs)
                            v₂ = showIx n ix
                        put (Map.insert n (ix+1) ixs)
                        return (Bind n v₂, \v₃ -> if v₃ == v₁ then Var v₂ else f v₃))

