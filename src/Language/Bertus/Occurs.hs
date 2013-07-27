module Language.Bertus.Occurs
    ( VarOrMeta
    , Occurrence(..)
    , isStrongRigid
    , isRigid
    , isFlexible
    , Occurs(..)
    , fvs
    , fmvs
    , nestVarOrMetas
    , pullVarOrMetas
    ) where

import Data.Data (Data, Typeable)
import Data.Monoid (Monoid(..), (<>), mconcat)

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Var
import Language.Bertus.Common
import Language.Bertus.Tm

#include "../../impossible.h"

type VarOrMeta = Either Meta

toVarOrMeta :: Head v -> VarOrMeta v
toVarOrMeta (Var v _) = Right v
toVarOrMeta (Meta mv) = Left mv

data Strength = Weak | Strong
    deriving (Show, Read, Eq, Ord, Data, Typeable)

data Occurrence = Flexible | Rigid Strength
    deriving (Show, Read, Eq, Ord, Data, Typeable)

isStrongRigid :: Maybe Occurrence -> Bool
isStrongRigid (Just (Rigid Strong)) = True
isStrongRigid _                     = False

isRigid :: Maybe Occurrence -> Bool
isRigid (Just (Rigid _)) = True
isRigid _                = False

isFlexible :: Maybe Occurrence -> Bool
isFlexible (Just Flexible) = True
isFlexible _               = False

instance Monoid Occurrence where
    mempty  = Flexible
    mappend = max

class Ord (OccursVar t) => Occurs t where
    type OccursVar t :: *
    occurrence :: Set (VarOrMeta (OccursVar t)) -> t -> Maybe Occurrence
    frees      :: t -> Set (VarOrMeta (OccursVar t))

fvs :: Occurs t => t -> Set (OccursVar t)
fvs = mapMaybeMonotonic (either (const Nothing) Just) . frees

fmvs :: Occurs t => t -> Set Meta
fmvs = mapMaybeMonotonic (either Just (const Nothing)) . frees

nestVarOrMetas :: Set (VarOrMeta v) -> Set (VarOrMeta (Var a v))
nestVarOrMetas = Set.mapMonotonic nest

pullVarOrMetas :: Set (VarOrMeta (Var a v)) -> Set (VarOrMeta v)
pullVarOrMetas = mapMaybeMonotonic f
  where
    f (Right (B _)) = Nothing
    f (Right (F v)) = Just (Right v)
    f (Left  mv   ) = Just (Left mv)

instance Ord v => Occurs (Tm v) where
    type OccursVar (Tm v) = v

    occurrence _ Type =
        Nothing
    occurrence vs (Bind _ lhs rhs) =
        occurrence vs lhs <> occurrence (nestVarOrMetas vs) rhs
    occurrence vs (Pair fs sn) =
        occurrence vs fs <> occurrence vs sn
    occurrence vs (Lam t) =
        occurrence (nestVarOrMetas vs) t
    occurrence vs (Neutr (Var v _) els) =
        if Right v `Set.member` vs then Just (Rigid Strong)
        else weaken <$> occurrence vs els
      where
        weaken (Rigid _) = Rigid Weak
        weaken Flexible  = Flexible
    occurrence vs (Neutr (Meta mv) els) =
        if Left mv `Set.member` vs then Just (Rigid Strong)
        else const Flexible <$> occurrence vs els

    frees Type             = mempty
    frees (Bind _ lhs rhs) = frees lhs <> pullVarOrMetas (frees rhs)
    frees (Pair fs sn    ) = frees fs  <> frees sn
    frees (Lam t         ) = pullVarOrMetas (frees t)
    frees (Neutr v els)    = Set.insert (toVarOrMeta v) (frees els)

instance Ord v => Occurs (Elim v) where
    type OccursVar (Elim v) = v

    occurrence vs (App t) = occurrence vs t
    occurrence _  _       = Nothing

    frees (App t) = frees t
    frees _       = Set.empty

instance Occurs t => Occurs [t] where
    type OccursVar [t] = OccursVar t

    occurrence vs = mconcat . map (occurrence vs)
    frees         = mconcat . map frees

instance (Occurs a, Occurs b, OccursVar a ~ OccursVar b) => Occurs (a, b) where
    type OccursVar (a, b) = OccursVar a
    occurrence vs (a, b) = occurrence vs a <> occurrence vs b
    frees (a, b) = frees a <> frees b

instance (Occurs a, Occurs b, Occurs c, OccursVar a ~ OccursVar b, OccursVar b ~ OccursVar c) => Occurs (a, b, c) where
    type OccursVar (a, b, c) = OccursVar a
    occurrence vs (a, b, c) =
        occurrence vs a <> occurrence vs b <> occurrence vs c
    frees (a, b, c) = frees a <> frees b <> frees c
