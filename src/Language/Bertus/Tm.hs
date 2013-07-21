module Language.Bertus.Tm
    ( module Data.Var
    , Name
    , Scope
    , Tm(..)
    , Ty
    , Meta
    , Head(..)
    , var
    , Twin(..)
    , Binder(..)
    , Elim(..)
    ) where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Data (Data, Typeable)

import Control.Monad.Fresh
import Data.Var

#include "../../impossible.h"

type Name = String

type Scope f v = f (Var Name v)

data Tm v
    = Type
    | Lam (Scope Tm v)
    | Neutr (Head v) [Elim v]
    | Binder Binder (Tm v) (Scope Tm v)
    | Pair (Tm v) (Tm v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

type Ty = Tm

newtype Meta = M Ref
    deriving (Eq, Ord, Show, Data, Typeable)

data Head v = Var v Twin | Meta Meta
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

var :: Head v -> Tm v
var v = Neutr v []

data Twin = Only | TwinL | TwinR
    deriving (Eq, Ord, Show, Data, Typeable)

data Binder = Pi | Sig
    deriving (Eq, Ord, Show, Data, Typeable)

data Elim v = App (Tm v) | Fst | Snd
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

