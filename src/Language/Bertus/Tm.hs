module Language.Bertus.Tm
    ( module Data.Var
    , Name
    , name
    , Scope
    , Tm(..)
    , Ty
    , (-->)
    , Meta
    , meta
    , Head0(..)
    , Head
    , head_
    , var
    , var'
    , metavar
    , Twin(..)
    , Bind(..)
    , Elim(..)
    ) where

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Data (Data, Typeable)

import Control.Monad.Fresh
import Data.Dummy
import Data.Var

type Name = Dummy String

name :: String -> Name
name = Dummy

type Scope f v = f (Var Name v)

data Tm v
    = Type
    | Bind Bind (Tm v) (Scope Tm v)
    | Pair (Tm v) (Tm v)
    | Lam (Scope Tm v)
    | Neutr (Head v) [Elim v]
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

type Ty = Tm

(-->) :: Tm v -> Tm v -> Tm v
dom --> cod = Bind Pi dom (fmap F cod)

newtype Meta = M Ref
    deriving (Eq, Ord, Show, Data, Typeable)

meta :: Ref -> Meta
meta = M

data Head0 tw v = Var v tw | Meta Meta
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

type Head = Head0 Twin

head_ :: Head v -> Tm v
head_ v = Neutr v []

var :: v -> Twin -> Tm v
var v tw = head_ (Var v tw)

var' :: v -> Tm v
var' v = var v Only

metavar :: Meta -> Tm v
metavar mv = Neutr (Meta mv) []

data Twin = Only | TwinL | TwinR
    deriving (Eq, Ord, Show, Data, Typeable)

data Bind = Pi | Sig
    deriving (Eq, Ord, Show, Data, Typeable)

data Elim v = App (Tm v) | Fst | Snd
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)
