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
cursFree Cursor{cursPull = pull, cursNest = nest} v = v == nest (pull v)

newCurs :: Cursor f Id
newCurs = Cursor{ cursPull   = id
                , cursNest   = id
                , cursRename = flip ($)
                , cursCtx    = const IMPOSSIBLE("looking up an empty ctx") }

nestCurs :: Functor f => Cursor f v -> f v -> Cursor f (Var (Name Id ()) v)
nestCurs Cursor{ cursPull   = pull
               , cursNest   = nest
               , cursRename = rename
               , cursCtx    = ctx } t =
    Cursor{ cursPull   = \v -> case v of B n -> name n; F v' -> pull v'
          , cursNest   = F . nest
          , cursRename = \v f -> case v of B (Name n ()) -> B (Name (f n) ())
                                           F v'          -> F (rename v' f)
          , cursCtx    = \v -> case v of B _  -> F <$> t
                                         F v' -> F <$> ctx v'
          }

nestCursP :: CursorP v -> CursorP (Var (Name Id ()) v)
nestCursP = flip nestCurs Proxy

toCursP :: Cursor f v -> CursorP v
toCursP Cursor{cursPull = pull, cursNest = nest, cursRename = rename} =
    Cursor{ cursPull   = pull
          , cursNest   = nest
          , cursRename = rename
          , cursCtx    = const Proxy
          }
