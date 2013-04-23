-- TODO I can greatly improve the efficiency of this:
--   * Condense cycles of <=
--   * Prune vertices of variables that do not appear anymore, preserving the
--     paths.
module Kant.Constraint
    ( Constr(..)
    , Constrs
    , empty
    , addConstr
    , addConstrs
    ) where

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

newtype Constrs a = Constrs (Graph a ConstrTy)

data Constr a = a :<=: a | a :<: a | a :==: a

empty :: Constrs a
empty = Constrs Graph.empty

addConstr :: (Eq a, Hashable a, Show a) => Constr a -> Constrs a -> Maybe (Constrs a)
addConstr c (Constrs oldGr) =
    if consistent newGr then Just (Constrs newGr) else Nothing
  where
    newGr = foldr Graph.addEdge oldGr (edges c)

    edges (r₁ :<=: r₂) = [(r₁, Weak, r₂)]
    edges (r₁ :<:  r₂) = [(r₁, Strong, r₂)]
    edges (r₁ :==: r₂) = [(r₁, Weak, r₂), (r₂, Weak, r₁)]

addConstrs :: (Eq a, Hashable a, Show a) => [Constr a] -> Constrs a -> Maybe (Constrs a)
addConstrs = flip (foldrM addConstr)

consistent :: (Eq a, Hashable a, Show a) => Graph a ConstrTy -> Bool
consistent gr = all weakCycle (Graph.scc gr)
  where
    weakCycle (Graph.Acyclic _) = True
    weakCycle (Graph.Cyclic vs) =
        all (\(_, cty, _) -> cty == Weak) (Graph.inEdges vs gr)
