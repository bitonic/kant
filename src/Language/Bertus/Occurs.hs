module Language.Bertus.Occurs
    ( Occurrence(..)
    , Occurs(..)
    , occurrenceList
    , occurrenceScope
    , freesScope
    ) where

import Data.Data (Data, Typeable)
import Data.Monoid (Monoid(..), (<>), mconcat)

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Var
import Language.Bertus.Common
import Language.Bertus.Tm

#include "../../impossible.h"

type VarMeta = Head0 ()

toVarMeta :: Head0 a v -> VarMeta v
toVarMeta (Var v _) = Var v ()
toVarMeta (Meta mv) = Meta mv

data Strength = Weak | Strong
    deriving (Show, Read, Eq, Ord, Data, Typeable)

data Occurrence = Flexible | Rigid Strength
    deriving (Show, Read, Eq, Ord, Data, Typeable)

instance Monoid Occurrence where
    mempty  = Flexible
    mappend = max

class Occurs t where
    occurrence :: Ord v => Set (VarMeta v) -> t v -> Maybe Occurrence
    frees      :: Ord v => t v -> Set (VarMeta v)

-- Safe use of `mapMonotonic': we're wrapping `Var's with `F'.
nestVarMetas :: Set (VarMeta v) -> Set (VarMeta (Var a v))
nestVarMetas = Set.mapMonotonic nest

-- Safe use of `mapMonotonic': we're unwrapping `Var's.
pullVarMetas :: Set (VarMeta (Var a v)) -> Set (VarMeta v)
pullVarMetas = Set.mapMonotonic g . Set.filter f
  where
    f (Var (B _) _) = False
    f _             = True

    g (Var (B _) _ ) = IMPOSSIBLE("We removed all the bound")
    g (Var (F v) tw) = Var v tw
    g (Meta mv     ) = Meta mv

instance Occurs Tm where
    occurrence _ Type =
        Nothing
    occurrence vs (Bind _ lhs rhs) =
        occurrence vs lhs <> occurrenceScope vs rhs
    occurrence vs (Pair fs sn) =
        occurrence vs fs <> occurrence vs sn
    occurrence vs (Lam t) =
        occurrenceScope vs t
    occurrence vs (Neutr (Var v _) els) =
        if Var v () `Set.member` vs then Just (Rigid Strong)
        else weaken <$> occurrenceList vs els
      where
        weaken (Rigid _) = Rigid Weak
        weaken Flexible  = Flexible
    occurrence vs (Neutr (Meta mv) els) =
        if Meta mv `Set.member` vs then Just (Rigid Strong)
        else const Flexible <$> occurrenceList vs els

    frees Type             = mempty
    frees (Bind _ lhs rhs) = frees lhs <> freesScope rhs
    frees (Pair fs sn    ) = frees fs  <> frees sn
    frees (Lam t         ) = freesScope t
    frees (Neutr v els)    = mconcat $
                             Set.singleton (toVarMeta v) : map (frees) els

occurrenceList :: (Ord v, Occurs t)
               => Set (VarMeta v) -> [t v] -> Maybe Occurrence
occurrenceList _  []  = Nothing
occurrenceList vs els = mconcat (map (occurrence vs) els)

occurrenceScope :: (Ord v, Occurs t)
                => Set (VarMeta v) -> Scope t v -> Maybe Occurrence
occurrenceScope vs = occurrence (nestVarMetas vs)

freesScope :: (Ord v, Occurs t) => Scope t v -> Set (VarMeta v)
freesScope = pullVarMetas . frees

instance Occurs Elim where
    occurrence vs (App t) = occurrence vs t
    occurrence _  _       = Nothing

    frees (App t) = frees t
    frees _       = Set.empty
