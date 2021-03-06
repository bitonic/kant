-- | Handles a system of constraints, detecting inconsistencies when they
--   arise.
--
--   Supports @<@, @<=@, and @==@ constraints, with the behaviour you would
--   expect from those constraints on integers.
module Data.Constraint
    ( Constr(..)
    , Constrs
    , empty
    , addConstr
    , addConstrs
    ) where

import           Control.Applicative ((<$>))
import           Data.Foldable (foldrM)

import           Data.Hashable (Hashable(..))

import           Data.LGraph (Graph)
import qualified Data.LGraph as Graph

data ConstrTy = Weak | Strong
    deriving (Eq, Show)

instance Ord ConstrTy where
    Weak   `compare` Strong = LT
    Strong `compare` Weak   = GT
    _      `compare` _      = EQ

instance Hashable ConstrTy where
    hashWithSalt i Weak   = hashWithSalt i True
    hashWithSalt i Strong = hashWithSalt i False

-- | Data type holding the set of constraints, parametrised over the
--   type of the variables.
newtype Constrs a = Constrs (Graph a ConstrTy)

data Constr a = a :<=: a | a :<: a | a :==: a

-- | An empty set of constraints.
empty :: Constrs a
empty = Constrs Graph.empty

-- | Adds one constraint to the set, returns the new set of constraints
--   if consistent.
addConstr :: (Eq a, Hashable a) => Constr a -> Constrs a -> Maybe (Constrs a)
addConstr c (Constrs oldGr) = Constrs <$> consistent newGr
  where
    newGr = foldr Graph.addEdge oldGr (edges c)

    edges (r₁ :<=: r₂) = [(r₁, Weak, r₂)]
    edges (r₁ :<:  r₂) = [(r₁, Strong, r₂)]
    edges (r₁ :==: r₂) = [(r₁, Weak, r₂), (r₂, Weak, r₁)]

addConstrs :: (Eq a, Hashable a) => [Constr a] -> Constrs a -> Maybe (Constrs a)
addConstrs = flip (foldrM addConstr)

consistent :: (Eq a, Hashable a) => Graph a ConstrTy -> Maybe (Graph a ConstrTy)
consistent gr =
    if all weakCycle sccs
    then Just (Graph.condenseAll sccs gr)
    else Nothing
  where
    sccs = Graph.scc gr

    weakCycle (Graph.Acyclic _) = True
    weakCycle (Graph.Cyclic vs) =
        all (\(_, cty, _) -> cty == Weak) (Graph.inEdges vs gr)
