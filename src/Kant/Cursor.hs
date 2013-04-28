module Kant.Cursor
    ( Ctx
    , Cursor(..)
    , CursorT
    , CursorId
    , CursorP
    , cursFree
    , newCurs
    , nestCurs
    , nestCursP
    , toCursP
    , IsCursor(..)
    , nestC
    , restoreC
    , toP
    , nest
    , pull
    ) where

import           Control.Applicative ((<$>))

import           Bound
import           Bound.Name
import           Data.Proxy

import           Kant.Term
#include "../impossible.h"

type Ctx f v = v -> f v

data Cursor f v = Cursor
    { cursPull   :: v -> Id
    , cursNest   :: Id -> v
    , cursRename :: v -> (Id -> Id) -> v
    , cursCtx    :: Ctx f v
    }

type CursorT = Cursor TermRef
type CursorId = Cursor TermRef Id
type CursorP = Cursor Proxy

cursFree :: Eq v => Cursor f v -> v -> Bool
cursFree Cursor{cursPull = pull_, cursNest = nest_} v = v == nest_ (pull_ v)

newCurs :: Cursor f Id
newCurs = Cursor{ cursPull   = id
                , cursNest   = id
                , cursRename = flip ($)
                , cursCtx    = const IMPOSSIBLE("looking up an empty ctx") }

nestCurs :: Functor f => Cursor f v -> f v -> Cursor f (Var (Name Id ()) v)
nestCurs Cursor{ cursPull   = pull_
               , cursNest   = nest_
               , cursRename = rename
               , cursCtx    = ctx } t =
    Cursor{ cursPull   = \v -> case v of B n -> name n; F v' -> pull_ v'
          , cursNest   = F . nest_
          , cursRename = \v f -> case v of B (Name n ()) -> B (Name (f n) ())
                                           F v'          -> F (rename v' f)
          , cursCtx    = \v -> case v of B _  -> F <$> t
                                         F v' -> F <$> ctx v'
          }

nestCursP :: CursorP v -> CursorP (Var (Name Id ()) v)
nestCursP = flip nestCurs Proxy

toCursP :: Cursor f v -> CursorP v
toCursP Cursor{cursPull = pull_, cursNest = nest_, cursRename = rename} =
    Cursor{ cursPull   = pull_
          , cursNest   = nest_
          , cursRename = rename
          , cursCtx    = const Proxy
          }

class IsCursor c where
    getCurs :: c f v -> Cursor f v
    putCurs :: Cursor f v -> c f' v' -> c f v

instance IsCursor Cursor where
    getCurs = id
    putCurs c _ = c

nestC :: (IsCursor c, Functor f) => c f v -> f v -> c f (Var (Name Id ()) v)
nestC c t = putCurs (nestCurs (getCurs c) t) c

restoreC :: (IsCursor c) => c f v -> c f' v' -> c f v
restoreC c c' = putCurs (getCurs c) c'

toP :: (IsCursor c) => c f v -> c Proxy v
toP c = putCurs (toCursP (getCurs c)) c

nest :: IsCursor c => c f v -> Id -> v
nest c = cursNest (getCurs c)

pull :: IsCursor c => c f v -> v -> Id
pull c = cursPull (getCurs c)
