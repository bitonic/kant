{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Language.Bertus.Tm
    ( module Data.Var
    , Scope
    , Tm(..)
    , Ty
    , Meta
    , Head(..)
    , var
    , Twin(..)
    , Binder(..)
    , Elim(..)
    , Subst(..)
    , inst
    , subst
    , nest
    , (%%)
    , (%%%)
    ) where

import Data.Traversable (Traversable)
import Data.Foldable (Foldable)

import Control.Monad.Fresh
import Data.Var

#include "../../impossible.h"

type UName = String
type UVar = Var UName

type Scope f v = f (UVar v)

data Tm v
    = Type
    | Lam (Scope Tm v)
    | Neutr (Head v) [Elim v]
    | Binder Binder (Tm v) (Scope Tm v)
    | Pair (Tm v) (Tm v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type Ty = Tm

type Meta = Ref

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

infixl 1 //=

class Subst f where
    (//=) :: f a -> (Head a -> Tm b) -> f b

instance Subst Tm where
    Type              //= _ = Type
    Lam s             //= f = Lam (s //= nest f)
    Neutr v els       //= f = f v %%% map (//= f) els
    Binder bi lhs rhs //= f = Binder bi (lhs //= f) (rhs //= nest f)
    Pair t u          //= f = Pair (t //= f) (u //= f)

instance Subst Elim where
    App t //= f = App (t //= f)
    Fst   //= _ = Fst
    Snd   //= _ = Snd

inst :: Subst f => f (Var a v) -> Tm v -> f v
inst s t = s //= \v -> case v of
                           Var  (B _ ) _    -> t
                           Var  (F v') tw   -> var (Var v' tw)
                           Meta me          -> var (Meta me)

subst :: (Eq v, Subst f) => Head v -> Tm v -> f v -> f v
subst v t u = u //= \v' -> if v == v' then t else var v'

nest :: (Head t -> Tm v) -> Head (Var a t) -> Tm (Var a v)
nest _ (Var  (B x) tw) = var (Var (B x) tw)
nest f (Var  (F v) tw) = f (Var v tw) //= (var . fmap F)
nest _ (Meta me)       = var (Meta me)

(%%) :: Tm v -> Elim v -> Tm v
Pair t _    %% Fst   = t
Pair _ u    %% Snd   = u
Lam s       %% App t = inst s t
Neutr v els %% el    = Neutr v (els ++ [el])
_           %% _     = IMPOSSIBLE("Bad elimination")

(%%%) :: Tm v -> [Elim v] -> Tm v
(%%%) = foldl (%%)
