{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.Term
    ( Id
    , ConId
    , HoleId
    , NameId
    , Ref
    , TmScope
    , TmScopeRef
    , Tm(..)
    , ADTRec(..)
    , TmRef
    , TmId
    , TmRefId
    , TmSyn
      -- * Smart constructors
    , lam
    , arr
    , app
      -- * Smart destructors
    , appV
    , appHead
    , binding
    , bindingN
    , dummyN
    , scopeV
    , scopeN
    , arrLen
    , annV
      -- * Utils
    , mapRef
    , unRef
      -- * Holes
    , isHole
    , HoleCtx(..)
      -- * Variables
    , VarC
    ) where

import           Data.Foldable (Foldable, foldl1)
import           Data.Traversable (Traversable)
import           Prelude hiding (foldl1)

import           Control.Monad.Identity (runIdentity)

import           Bound
import           Bound.Name
import           Bound.Scope
import           Data.Hashable (Hashable)
import           Prelude.Extras

import           Kant.Common
#include "../impossible.h"

type Id = String
type ConId = Id
type HoleId = String
type NameId = Name Id ()

type Ref = Integer

type TmScope r = Scope NameId (Tm r)
type TmScopeRef = TmScope Ref

-- TODO make the treatment of holes better---e.g. don't let them escape their
-- enironment
data Tm r v
    = V v
    | Ty r
    | Lam (TmScope r v)
    | Arr (Tm r v) (TmScope r v)
    | App (Tm r v) (Tm r v)
    | Ann (Tm r v) (Tm r v)
    | Con ADTRec ConId ConId [Tm r v]
    | Destr ADTRec ConId Id (Tm r v)
    | Hole HoleId [Tm r v]
    | TyEq (Tm r v) (Tm r v)
    | HeEq (Tm r v) (Tm r v) (Tm r v) (Tm r v)
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

data ADTRec = ADT_ | Rec_
    deriving (Eq, Ord, Show, Read)

type TmRef = Tm Ref
type TmId r = Tm r Id
type TmRefId = TmRef Id
type TmSyn = Tm () Id

instance (Eq r)   => Eq1 (Tm r)   where (==#)      = (==)
instance (Ord r)  => Ord1 (Tm r)  where compare1   = compare
instance (Show r) => Show1 (Tm r) where showsPrec1 = showsPrec
instance (Read r) => Read1 (Tm r) where readsPrec1 = readsPrec

instance Monad (Tm r) where
    return = V

    V v                >>= f = f v
    Ty r               >>= _ = Ty r
    Lam s              >>= f = Lam (s >>>= f)
    Arr ty s           >>= f = Arr (ty >>= f) (s >>>= f)
    App t₁ t₂          >>= f = App (t₁ >>= f) (t₂ >>= f)
    Con ar tyc dc ts   >>= f = Con ar tyc dc (map (>>= f) ts)
    Destr ar tyc n t   >>= f = Destr ar tyc n (t >>= f)
    Ann ty t           >>= f = Ann (ty >>= f) (t >>= f)
    Hole hn ts         >>= f = Hole hn (map (>>= f) ts)
    TyEq ty₁ ty₂       >>= f = TyEq (ty₁ >>= f) (ty₂ >>= f)
    HeEq t₁ ty₁ t₂ ty₂ >>= f = HeEq (t₁ >>= f) (ty₁ >>= f) (t₂ >>= f) (ty₂ >>= f)

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

scopeV :: TmScope r v -> (NameId -> Tm r v) -> (Maybe NameId, Tm r v)
scopeV s f =
    case bindings s of
        []      -> (Nothing, instantiate1 IMPOSSIBLE("the impossible happened") s)
        (n : _) -> (Just n, instantiate1 (f n) s)

scopeN :: TmScope r Id -> (Maybe Id, TmId r)
scopeN s = (name <$> mn, t) where (mn, t) = scopeV s (\(Name n _) -> V n)

arrLen :: Tm r v -> Int
arrLen (Arr _ s) = 1 + arrLen (fromScope s)
arrLen _         = 0

annV :: Tm r t -> Tm r t
annV (Ann _ t) = t
annV t         = t

mapRef :: (Monad m)  => (r₁ -> m r₂) -> Tm r₁ v -> m (Tm r₂ v)
mapRef _ (V v)                = return (V v)
mapRef f (Ty r)               = Ty <$> f r
mapRef f (Lam s)              = Lam . toScope <$> mapRef f (fromScope s)
mapRef f (Arr t s)            = Arr <$> mapRef f t
                                    <*> (toScope <$> mapRef f (fromScope s))
mapRef f (App t₁ t₂)          = App <$> mapRef f t₁ <*> mapRef f t₂
mapRef f (Ann ty t)           = Ann <$> mapRef f ty <*> mapRef f t
mapRef f (Con ar tyc dc ts)   = Con ar tyc dc <$> mapM (mapRef f) ts
mapRef f (Destr ar tyc n t)   = Destr ar tyc n <$> mapRef f t
mapRef f (Hole h ts)          = Hole h <$> mapM (mapRef f) ts
mapRef f (TyEq ty₁ ty₂)       = TyEq <$> mapRef f ty₁ <*> mapRef f ty₂
mapRef f (HeEq t₁ ty₁ t₂ ty₂) = HeEq <$> mapRef f t₁ <*> mapRef f ty₁
                                     <*> mapRef f t₂ <*> mapRef f ty₂

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
