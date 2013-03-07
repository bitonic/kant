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
    , TermScope
    , Term(..)
    , TermId
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
      -- * Holes
    , isHole
    , HoleCtx(..)
    ) where

import           Control.Applicative ((<$>))
import           Data.Foldable (Foldable)
import           Data.Traversable (Traversable)

import           Bound
import           Bound.Name
import           Bound.Scope
import           Prelude.Extras

type Id = String
type ConId = Id
type HoleId = String
type NameId = Name Id

type TermScope = Scope (NameId ()) Term

data Term v
    = V v
    | Ty
    | Lam (TermScope v)
    | Arr (Term v) (TermScope v)
    | App (Term v) (Term v)
    | Ann (Term v) (Term v)
    | Canon ConId [Term v]
    | Elim ConId [Term v]
    | Hole HoleId [Term v]
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

type TermId = Term Id

instance Eq1 Term   where (==#)      = (==)
instance Ord1 Term  where compare1   = compare
instance Show1 Term where showsPrec1 = showsPrec
instance Read1 Term where readsPrec1 = readsPrec

instance Monad Term where
    return = V

    V v        >>= f = f v
    Ty         >>= _ = Ty
    Lam s      >>= f = Lam (s >>>= f)
    Arr ty s   >>= f = Arr (ty >>= f) (s >>>= f)
    App t₁ t₂  >>= f = App (t₁ >>= f) (t₂ >>= f)
    Canon c ts >>= f = Canon c (map (>>= f) ts)
    Elim c ts  >>= f = Elim c (map (>>= f) ts)
    Ann ty t   >>= f = Ann (ty >>= f) (t >>= f)
    Hole hn ts >>= f = Hole hn (map (>>= f) ts)

lam :: Maybe Id -> TermId -> TermId
lam Nothing  t = Lam (toScope (F <$> t))
lam (Just v) t = Lam (abstract1Name v t)

arr :: Maybe Id -> TermId -> TermId -> TermId
arr Nothing  ty t = Arr ty (toScope (F <$> t))
arr (Just v) ty t = Arr ty (abstract1Name v t)

app :: [Term v] -> Term v
app = foldl1 App

appV :: Term v -> (Term v, [Term v])
appV (App t₁ t₂) = (t, ts ++ [t₂]) where (t, ts) = appV t₁
appV t = (t, [])

appHead :: Term v -> Term v
appHead (appV -> (t, _)) = t

binding :: Scope (NameId ()) Term v -> Maybe (NameId ())
binding s = case bindings s of
                []      -> Nothing
                (n : _) -> Just n

bindingN :: Scope (NameId ()) Term v -> NameId ()
bindingN s = case bindings s of
                 []      -> dummyN
                 (n : _) -> n

dummyN :: NameId ()
dummyN = Name "$" ()

scopeV :: Scope (NameId ()) Term v -> (NameId () -> Term v)
       -> (Maybe (NameId ()), Term v)
scopeV s f =
    case bindings s of
        []      -> (Nothing, instantiate1 (error "scopeV: the impossible happened") s)
        (n : _) -> (Just n, instantiate1 (f n) s)

scopeN :: Scope (NameId ()) Term Id -> (Maybe Id, TermId)
scopeN s = (name <$> mn, t) where (mn, t) = scopeV s (\(Name n _) -> V n)

arrLen :: Term v -> Int
arrLen (Arr _ s) = 1 + arrLen (fromScope s)
arrLen _         = 0

annV :: Term t -> Term t
annV (Ann _ t) = t
annV t         = t

isHole :: Term v -> Bool
isHole (Hole _ _) = True
isHole _          = False

data HoleCtx = HoleCtx
    { holeName :: HoleId
    , holeGoal :: TermId
    , holeCtx  :: [(TermId, TermId)]
    }
