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
    , Head(..)
    , head_
    , var
    , var'
    , metavar
    , Twin(..)
    , Bind(..)
    , Elim(..)
    , boundName
    , unnest
    , etaContract
    , isVar
    , toVars
    , occursIn
    , linearOn
    ) where

import Data.Foldable (Foldable, foldMap)
import Data.Traversable (Traversable, traverse)
import Data.Data (Data, Typeable)
import Data.Monoid (Any(..))

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

data Head v = Var v Twin | Meta Meta
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

head_ :: Head v -> Tm v
head_ v = Neutr v []

data Twin = Only | TwinL | TwinR
    deriving (Eq, Ord, Show, Data, Typeable)

data Bind = Pi | Sig
    deriving (Eq, Ord, Show, Data, Typeable)

data Elim v = App (Tm v) | Fst | Snd
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

mapElim :: (Tm a -> Tm b) -> Elim a -> Elim b
mapElim = undefined

var :: v -> Twin -> Tm v
var v tw = head_ (Var v tw)

var' :: v -> Tm v
var' v = var v Only

metavar :: Meta -> Tm v
metavar mv = Neutr (Meta mv) []

boundName :: Scope f v -> Name
boundName = undefined

unnest :: Traversable f => Scope f v -> Maybe (f v)
unnest = traverse f
  where
    f (B _) = Nothing
    f (F v) = Just v

initLast :: [a] -> Maybe ([a], a)
initLast [] = Nothing
initLast xs = Just (init xs, last xs)

etaContract :: Ord v => Tm v -> Tm v
etaContract (Lam t) =
    case etaContract t of
        Neutr (unnest -> Just v1) els
            | Just (els', App (Neutr (Var (B _) _) [])) <- initLast els
            , Just els'' <- traverse unnest els' ->
            Neutr v1 els''
        t' -> Lam t'
etaContract (Neutr v els) =
    Neutr v (map (mapElim etaContract) els)
etaContract (Pair fs sn) =
    case (etaContract fs, etaContract sn) of
        (Neutr v1 els1, Neutr v2 els2)
            | Just (els1', Fst) <- initLast els1
            , Just (els2', Snd) <- initLast els2
            , v1 == v2
            , els1' == els2' ->
            Neutr v1 els1'
        (fs', sn') -> Pair fs' sn'
etaContract (Bind bi lhs rhs) =
    Bind bi (etaContract lhs) (etaContract rhs)
etaContract Type =
    Type

isVar :: Ord v => Tm v -> Bool
isVar (etaContract -> Neutr (Var _ _) []) = True
isVar _                                   = False

toVars :: Ord v => [Elim v] -> Maybe [v]
toVars = traverse (toVar . mapElim etaContract)
  where
    toVar (App (Neutr (Var v _) [])) = Just v
    toVar _                          = Nothing

occursIn :: (Traversable f, Eq v) => v -> f v -> Bool
v `occursIn` t = getAny (foldMap (Any . (v ==)) t)

linearOn :: Eq v => Tm v -> [v] -> Bool
linearOn _ [] = True
linearOn t (v : vs) = not (v `occursIn` t) && linearOn t vs
