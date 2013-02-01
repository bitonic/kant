{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Kant.Fresh
    ( Fresh
    , bumpCount
    , freshName
    , runFresh
    ) where

import           Control.Applicative (Applicative)
import           Data.Maybe (fromMaybe)

import           Control.Monad.State (State, MonadState(..), evalState)
import           Data.Map (Map)
import qualified Data.Map as Map

import           Kant.Syntax

newtype Fresh a = Fresh (State (Map Id Int) a)
    deriving (Functor, Applicative, Monad)

bumpCount :: Id -> Fresh Int
bumpCount n = do m <- Fresh get
                 let i = fromMaybe 0 (Map.lookup n m)
                 Fresh (put (Map.insert n i m))
                 return i

freshName :: Id -> Fresh Id
freshName n = do i <- bumpCount n
                 return (n ++ if i == 0 then "" else show i)

runFresh :: Fresh a -> a
runFresh (Fresh st) = evalState st Map.empty
