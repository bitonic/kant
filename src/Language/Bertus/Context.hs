{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
module Language.Bertus.Context where

import Data.Traversable (Traversable)
import Data.Foldable (Foldable)

import Language.Bertus.Tm

data Decl v = Hole | Defn (Tm v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Eqn v = Eqn (Ty v) (Tm v) (Ty v) (Ty v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Problem v = Unify (Eqn v) | All (Param v) (Scope Problem v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Param v = Param (Ty v) | Twins (Ty v) (Ty v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

infixl 5 :>
data Fwd f g a v where
    F0   :: g v -> Fwd f g a v
    (:>) :: f v -> Fwd f g a (Var a v) -> Fwd f g a v
    deriving (Functor, Foldable, Traversable)

instance (Subst f, Subst g) => Subst (Fwd f g a) where
    F0 t     //= f = F0 (t //= f)
    ty :> te //= f = (ty //= f) :> (te //= nest f)

infixr 5 :<
data Bwd f g a v where
    B0   :: g v -> Bwd f g a v
    (:<) :: Bwd f g a v -> f v -> Bwd f g a (Var a v)

lookBwd :: Functor f => Bwd f g a v -> v -> Maybe (f v)
lookBwd (B0 _)    _     = Nothing
lookBwd (bw :< _) (F v) = fmap (fmap F) (lookBwd bw v)
lookBwd (_  :< t) (B _) = Just (fmap F t)
