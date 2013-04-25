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
    , TermScope
    , TermScopeRef
    , Term(..)
    , TermRef
    , TermId
    , TermRefId
    , TermSyn
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

import           Data.Foldable (Foldable)
import           Data.Traversable (Traversable)

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
type NameId = Name Id

type Ref = Integer

type TermScope r = Scope (NameId ()) (Term r)
type TermScopeRef = TermScope Ref

-- TODO make the treatment of holes better---e.g. don't treat them as normal
-- terms...
data Term r v
    = V v
    | Ty r
    | Lam (TermScope r v)
    | Arr (Term r v) (TermScope r v)
    | App (Term r v) (Term r v)
    | Ann (Term r v) (Term r v)
    | Canon ConId [Term r v]
    | Elim ConId [Term r v]
    | Hole HoleId [Term r v]
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

type TermRef = Term Ref
type TermId r = Term r Id
type TermRefId = TermRef Id
type TermSyn = Term () Id

instance (Eq r)   => Eq1 (Term r)   where (==#)      = (==)
instance (Ord r)  => Ord1 (Term r)  where compare1   = compare
instance (Show r) => Show1 (Term r) where showsPrec1 = showsPrec
instance (Read r) => Read1 (Term r) where readsPrec1 = readsPrec

instance Monad (Term r) where
    return = V

    V v        >>= f = f v
    Ty r       >>= _ = Ty r
    Lam s      >>= f = Lam (s >>>= f)
    Arr ty s   >>= f = Arr (ty >>= f) (s >>>= f)
    App t₁ t₂  >>= f = App (t₁ >>= f) (t₂ >>= f)
    Canon c ts >>= f = Canon c (map (>>= f) ts)
    Elim c ts  >>= f = Elim c (map (>>= f) ts)
    Ann ty t   >>= f = Ann (ty >>= f) (t >>= f)
    Hole hn ts >>= f = Hole hn (map (>>= f) ts)

lam :: Maybe Id -> TermId r -> TermId r
lam Nothing  t = Lam (toScope (F <$> t))
lam (Just v) t = Lam (abstract1Name v t)

arr :: Maybe Id -> TermId r -> TermId r -> TermId r
arr Nothing  ty t = Arr ty (toScope (F <$> t))
arr (Just v) ty t = Arr ty (abstract1Name v t)

app :: [Term r v] -> Term r v
app = foldl1 App

appV :: Term r v -> (Term r v, [Term r v])
appV (App t₁ t₂) = (t, ts ++ [t₂]) where (t, ts) = appV t₁
appV t = (t, [])

appHead :: Term r v -> Term r v
appHead (appV -> (t, _)) = t

binding :: TermScope r v -> Maybe (NameId ())
binding s = case bindings s of
                []      -> Nothing
                (n : _) -> Just n

bindingN :: TermScope r v -> NameId ()
bindingN s = case bindings s of
                 []      -> dummyN
                 (n : _) -> n

dummyN :: NameId ()
dummyN = Name "$" ()

scopeV :: TermScope r v -> (NameId () -> Term r v) -> (Maybe (NameId ()), Term r v)
scopeV s f =
    case bindings s of
        []      -> (Nothing, instantiate1 IMPOSSIBLE("the impossible happened") s)
        (n : _) -> (Just n, instantiate1 (f n) s)

scopeN :: TermScope r Id -> (Maybe Id, TermId r)
scopeN s = (name <$> mn, t) where (mn, t) = scopeV s (\(Name n _) -> V n)

arrLen :: Term r v -> Int
arrLen (Arr _ s) = 1 + arrLen (fromScope s)
arrLen _         = 0

annV :: Term r t -> Term r t
annV (Ann _ t) = t
annV t         = t

mapRef :: (Monad m) => (r₁ -> m r₂) -> Term r₁ v -> m (Term r₂ v)
mapRef _ (V v)         = return (V v)
mapRef f (Ty r)        = Ty <$> f r
mapRef f (Lam s)       = Lam . toScope <$> mapRef f (fromScope s)
mapRef f (Arr t s)     = Arr <$> mapRef f t <*> (toScope <$> mapRef f (fromScope s))
mapRef f (App t₁ t₂)   = App <$> mapRef f t₁ <*> mapRef f t₂
mapRef f (Ann ty t)    = Ann <$> mapRef f ty <*> mapRef f t
mapRef f (Canon dc ts) = Canon dc <$> mapM (mapRef f) ts
mapRef f (Elim dc ts)  = Elim dc <$> mapM (mapRef f) ts
mapRef f (Hole h ts)   = Hole h <$> mapM (mapRef f) ts

unRef :: Term r v -> Term () v
unRef = runIdentity . mapRef (const (return ()))

isHole :: Term r v -> Bool
isHole (Hole _ _) = True
isHole _          = False

data HoleCtx = HoleCtx
    { holeRef  :: Ref
    , holeName :: HoleId
    , holeGoal :: TermRefId
    , holeCtx  :: [(TermRefId, TermRefId)]
    }

class (Hashable v, Ord v) => VarC v
instance (Hashable a, Ord a) => VarC [a]
instance (Hashable a, Ord a) => VarC (Name n a)
instance (VarC b, VarC a) => VarC (Var b a)
