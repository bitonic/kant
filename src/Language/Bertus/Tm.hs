module Language.Bertus.Tm
    ( Name
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

import Control.Monad.Fresh
import Data.Var

type Name = String

type Scope f v = f (Var Name v)

data Tm v
    = Type
    | Lam (Scope Tm v)
    | Neutr (Head v) [Elim v]
    | Binder Binder (Tm v) (Scope Tm v)
    | Pair (Tm v) (Tm v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type Ty = Tm

newtype Meta = M Ref
    deriving (Eq, Ord, Show)

data Head v = Var v Twin | Meta Meta
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

var :: Head v -> Tm v
var v = Neutr v []

data Twin = Only | TwinL | TwinR
    deriving (Eq, Ord, Show)

data Binder = Pi | Sig
    deriving (Eq, Ord, Show)

data Elim v = App (Tm v) | Fst | Snd
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
