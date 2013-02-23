{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
-- TODO this is *really* ugly, I should really look for some good abstractions
-- and reimplement those functions.
-- TODO the Fix stuff is broken, since we do not consider the fact that the
-- arguments scope over the whole body.  I've marked the offending sites with
-- FIXME.
module Kant.Uniquify
    -- ( Uniquify(..)
    -- , UniqueM
    -- , runUniquify
    -- , Count
    -- , revert
    -- )
    where

import           Control.Applicative ((<$>))

import           Control.Monad.State (State, MonadState(..), evalState, runState)
import qualified Data.Text as Text

import           Kant.Term
-- import           Kant.Environment

type Count = Integer

type UniqueM = State Count

-- class Uniquify f where
--     uniquify :: f Void Id -> UniqueM (f Id Tag)

-- runUniquify :: Uniquify f => Env -> f Void Id -> (Env, f Id Tag)
-- runUniquify env@Env{envCount = c} t = (env{envCount = c'}, t')
--   where (t', c') = runState (uniquify t) c

fresh :: State Count Id
fresh = do ta <- get
           put (ta + 1)
           return (show ta)

uniquify :: (Functor f, Subst f) => f Id -> UniqueM (f Tag)
uniquify t =
    fmap Text.pack <$>
    subst Var
          (\v₁ f -> do v₂ <- fresh
                       return (v₂, \v₃ -> if v₃ == v₁ then Var v₂ else f v₃))
          t
