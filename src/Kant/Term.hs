{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.Term where
    -- ( Id
    -- , ConId
    -- , HoleId
    -- , NameId
    -- , Ref
    -- , TmScope
    -- , TmScopeRef
    -- , Tm(..)
    -- , Data(..)
    -- , dataId
    -- , TmRef
    -- , TmId
    -- , TmRefId
    -- , TmSyn
    --   -- * Smart constructors
    -- , lam
    -- , arr
    -- , app
    --   -- * Smart destructors
    -- , appV
    -- , appHead
    -- , binding
    -- , bindingN
    -- , dummyN
    -- , scopeV
    -- , scopeN
    -- , arrLen
    -- , annV
    --   -- * Utils
    -- , mapRef
    -- , unRef
    --   -- * Holes
    -- , isHole
    -- , HoleCtx(..)
    --   -- * Variables
    -- , VarC
    -- ) where

import           Control.Arrow ((***), (+++))
import           Data.Foldable (Foldable, foldl1)
import           Data.Monoid (Monoid(..))
import           Data.Traversable (Traversable)
import           Prelude hiding (foldl1)

import           Control.Monad.Identity (runIdentity)

import           Bound
import           Bound.Name
import           Bound.Scope
import           Data.Hashable (Hashable)
import           Prelude.Extras

import           Data.Bwd
import           Kant.Common
#include "../impossible.h"

type Id = String
type ConId = Id
type HoleId = String
type NameId = Name Id ()

type Ref = Integer

type TmScope r = Scope NameId (Tm r)
type TmScopeRef = TmScope Ref

-- TODO make the treatment of holes better---e.g. don't treat them as normal
-- terms...
data Tm r v
    = V (V v)
    | Ty r
    | Lam (TmScope r v)
    | Arr (Tm r v) (TmScope r v)
    | App (Tm r v) (Tm r v)
    | Ann (Tm r v) (Tm r v)
    | Data (ConId, Data) [Tm r v]
    | Hole HoleId [Tm r v]
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

data V v = Twin v Twin | Meta v
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

getV :: V v -> v
getV (Twin v _) = v
getV (Meta v)   = v

onlyV :: v -> Tm r v
onlyV v = V (Twin v Only)

data Twin = Only | TwinL | TwinR
    deriving (Eq, Ord, Show, Read)

data Data = TyCon ADTRec | DataCon ADTRec ConId | ADTRewr | RecRewr Id
    deriving (Eq, Ord, Show, Read)

data ADTRec = ADT_ | Rec
    deriving (Eq, Ord, Show, Read)

type TmRef = Tm Ref
type TmId r = Tm r Id
type TmRefId = TmRef Id
type TmSyn = Tm () Id
type Ty = Tm
type TyRef = Ty Ref

instance (Eq r)   => Eq1   (Tm r) where (==#)      = (==)
instance (Ord r)  => Ord1  (Tm r) where compare1   = compare
instance (Show r) => Show1 (Tm r) where showsPrec1 = showsPrec
instance (Read r) => Read1 (Tm r) where readsPrec1 = readsPrec

instance Monad (Tm r) where
    return v = V (Twin v Only)

    V v        >>= f = f (getV v)
    Ty r       >>= _ = Ty r
    Lam s      >>= f = Lam (s >>>= f)
    Arr ty s   >>= f = Arr (ty >>= f) (s >>>= f)
    App t₁ t₂  >>= f = App (t₁ >>= f) (t₂ >>= f)
    Data d ts  >>= f = Data d (map (>>= f) ts)
    Ann ty t   >>= f = Ann (ty >>= f) (t >>= f)
    Hole hn ts >>= f = Hole hn (map (>>= f) ts)

lam :: Maybe Id -> TmId r -> TmId r
lam Nothing  t = Lam (toScope (F <$> t))
lam (Just v) t = Lam (abstract1Name v t)

arr :: Maybe Id -> TmId r -> TmId r -> TmId r
arr Nothing  ty t = Arr ty (toScope (F <$> t))
arr (Just v) ty t = Arr ty (abstract1Name v t)

app :: Foldable t => t (Tm r v) -> Tm r v
app = foldl1 App

appV :: Tm r v -> (Tm r v, [Tm r v])
appV (App t₁ t₂) = (t, ts ++ [t₂]) where (t, ts) = appV t₁
appV t = (t, [])

appHead :: Tm r v -> Tm r v
appHead (appV -> (t, _)) = t

binding :: TmScope r v -> Maybe NameId
binding s = case bindings s of
                []      -> Nothing
                (n : _) -> Just n

bindingN :: TmScope r v -> NameId
bindingN s = case bindings s of
                 []      -> dummyN
                 (n : _) -> n

dummyN :: NameId
dummyN = Name "x" ()

-- TODO is it bad here that I can extract a twin variable and then replace it
-- with a normal one, for example in 'scopeN'?
scopeV :: TmScope r v -> (NameId -> Tm r v) -> (Maybe NameId, Tm r v)
scopeV s f =
    case bindings s of
        []      -> (Nothing, instantiate1 IMPOSSIBLE("the impossible happened") s)
        (n : _) -> (Just n, instantiate1 (f n) s)

scopeN :: TmScope r Id -> (Maybe Id, TmId r)
scopeN s = (name <$> mn, t) where (mn, t) = scopeV s (\(Name n _) -> return n)

arrLen :: Tm r v -> Int
arrLen (Arr _ s) = 1 + arrLen (fromScope s)
arrLen _         = 0

annV :: Tm r t -> Tm r t
annV (Ann _ t) = t
annV t         = t

mapRef :: (Monad m)  => (r₁ -> m r₂) -> Tm r₁ v -> m (Tm r₂ v)
mapRef _ (V v)       = return (V v)
mapRef f (Ty r)      = Ty <$> f r
mapRef f (Lam s)     = Lam . toScope <$> mapRef f (fromScope s)
mapRef f (Arr t s)   = Arr <$> mapRef f t <*> (toScope <$> mapRef f (fromScope s))
mapRef f (App t₁ t₂) = App <$> mapRef f t₁ <*> mapRef f t₂
mapRef f (Ann ty t)  = Ann <$> mapRef f ty <*> mapRef f t
mapRef f (Data d ts) = Data d <$> mapM (mapRef f) ts
mapRef f (Hole h ts) = Hole h <$> mapM (mapRef f) ts

unRef :: Tm r v -> Tm () v
unRef = runIdentity . mapRef (const (return ()))

isHole :: Tm r v -> Bool
isHole (Hole _ _) = True
isHole _          = False

data HoleCtx = HoleCtx
    { holeRef  :: Ref
    , holeName :: HoleId
    , holeGoal :: TmRefId
    , holeCtx  :: [(TmRefId, TmRefId)]
    }

class (Hashable v, Ord v, Show v) => VarC v
instance (Hashable a, Ord a, Show a) => VarC [a]
instance (Hashable a, Ord a, Show a, Show n) => VarC (Name n a)
instance (VarC b, VarC a) => VarC (Var b a)

data Problem v
    = All (Param v) (Problem (Var NameId v))
    | Unify (Equation v)
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

data Param v
    = P (TyRef v)
    | Twins (TyRef v) (TyRef v)
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

-- INVARIANT: Terms are always stored in WHNF here.
data Equation v = Eqn (TmRef v) (TyRef v) (TmRef v) (TyRef v)
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

sym :: Equation v -> Equation v
sym (Eqn ty₁ t₁ ty₂ t₂) = Eqn ty₂ t₂ ty₁ t₁

data Dec v = HOLE | DEFN (TmRef v)
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

type ProbRef = Ref

data ProblemState = Blocked | Active | Pending [ProbRef] | Solved | Failed
    deriving (Eq, Ord, Show, Read)

data Entry v
    = MV v (TyRef v) (Dec v)
    | Prob ProbRef (Problem v) ProblemState
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

type Subs v = [(v, TmRef v)]

data MCtx v = MCtx
    { mLeft  :: Bwd (Entry v)
    , mRight :: [Either (Subs v) (Entry v)]
    } deriving (Eq, Ord, Show, Read)

instance Monoid (MCtx v) where
    mempty = MCtx mempty mempty
    MCtx l₁ r₁ `mappend` MCtx l₂ r₂ = MCtx (l₁ `mappend` l₂) (r₁ `mappend` r₂)

instance Functor MCtx where
    fmap f (MCtx l r) =
        MCtx (fmap (fmap f) l) (map (map (f *** fmap f) +++ fmap f) r)
