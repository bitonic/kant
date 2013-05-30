-- | A module that provides a data structure and a typeclass to navigate
--   'Bound' terms, and associate something with each bound variable as we
--   enter 'Scope's.
module Kant.Cursor
    ( -- * Concrete types
      Ctx
    , Cursor(..)
    , CursorT
    , CursorId
    , CursorP
    , newCurs
      -- * Type class
    , IsCursor(..)
      -- ** Useful methods
    , nestC
    , restoreC
    , toP
    , nest
    , pull
    , free
    , free'
    , freeVs
    , ctx
    ) where

import           Control.Applicative ((<$>))
import           Data.Foldable (Foldable, foldMap)

import           Bound
import           Bound.Name
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import           Data.Proxy

import           Kant.Term
#include "../impossible.h"

type Ctx f v = v -> f v

data Cursor f v = Cursor
    { cursPull   :: v -> Id
      -- ^ Gets the 'Id' part of the 'Name' associated with a @v@.
    , cursNest   :: Id -> v
      -- ^ Nests an 'Id' to a @v@.  The result will be a @v@ referring to the
      --   'Id' as a top level thing.
    , cursRename :: v -> (Id -> Id) -> v
      -- ^ Modifyis the 'Id' part of the 'Name' associated with a @v@.
    , cursCtx    :: Ctx f v
      -- ^ Stores something parametrised on @v@ for each @v@.
    }

type CursorT = Cursor TmRef
type CursorId = Cursor TmRef Id

-- | It is useful to have a 'Cursor' with "empty" 'Ctx', if we want to use it
--   just to get 'cursPull', 'cursNest', and 'cursRename'.
--
--   The 'Proxy' indicates that we're not storing anything in the 'Ctx'.
type CursorP = Cursor Proxy

-- | Is the @v@ provided a free name?
cursFree :: Eq v => Cursor f v -> v -> Bool
cursFree Cursor{cursPull = pull_, cursNest = nest_} v = v == nest_ (pull_ v)

newCurs :: Cursor f Id
newCurs = Cursor{ cursPull   = id
                , cursNest   = id
                , cursRename = flip ($)
                , cursCtx    = const IMPOSSIBLE("looking up an empty ctx") }

-- | Give me a 'Cursor', and a function that associates a value for each bound
--   variable of the scope I'm entering, and I'll give you a cursor to work
--   inside a 'Scope' over a 'Var'.
nestCurs :: Functor f => Cursor f v -> (a -> f v) -> Cursor f (Var (Name Id a) v)
nestCurs Cursor{ cursPull   = pull_
               , cursNest   = nest_
               , cursRename = rename
               , cursCtx    = ctx_ } f =
    Cursor{ cursPull   = \v -> case v of B n -> name n; F v' -> pull_ v'
          , cursNest   = F . nest_
          , cursRename = \v g -> case v of
                                     B (Name n x) -> B (Name (g n) x)
                                     F v'         -> F (rename v' g)
          , cursCtx    = \v -> case v of
                                   B (Name _ x) -> F <$> f x
                                   F v'         -> F <$> ctx_ v'
          }

-- | Converts any @'Cursor' f@ to a @'Cursor' 'Proxy'@, by "emptying" the
--   'Ctx'.
toCursP :: Cursor f v -> CursorP v
toCursP Cursor{cursPull = pull_, cursNest = nest_, cursRename = rename} =
    Cursor{ cursPull   = pull_
          , cursNest   = nest_
          , cursRename = rename
          , cursCtx    = const Proxy
          }

-- | A type class for things with a cursor in it.
class IsCursor c where
    getCurs :: c f v -> Cursor f v
    putCurs :: Cursor f v -> c f' v' -> c f v

instance IsCursor Cursor where
    getCurs = id
    putCurs c _ = c

nestC :: (IsCursor c, Functor f) => c f v -> (a -> f v) -> c f (Var (Name Id a) v)
nestC c t = putCurs (nestCurs (getCurs c) t) c

restoreC :: (IsCursor c) => c f v -> c f' v' -> c f v
restoreC c c' = putCurs (getCurs c) c'

toP :: (IsCursor c) => c f v -> c Proxy v
toP c = putCurs (toCursP (getCurs c)) c

nest :: IsCursor c => c f v -> Id -> v
nest c = cursNest (getCurs c)

pull :: IsCursor c => c f v -> v -> Id
pull c = cursPull (getCurs c)

free :: (Eq v, IsCursor c) => c f v -> v -> Bool
free t = cursFree (getCurs t)

free' :: (Eq v, IsCursor c) => c f v -> v -> Maybe Id
free' c v = if free c v then Just (pull c v) else Nothing

freeVs :: (Eq v, IsCursor c, Foldable f) => c f v -> TmRef v -> HashSet Id
freeVs c = foldMap (\v -> if free c v
                          then HashSet.singleton (pull c v)
                          else HashSet.empty)

ctx :: IsCursor c => c f v -> Ctx f v
ctx = cursCtx . getCurs

