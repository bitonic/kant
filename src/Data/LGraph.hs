module Data.LGraph
    ( LGraph
    , Edge
    , empty
    , edges
    , addEdge
    , sccs
    ) where

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import           Data.Hashable (Hashable(..))

type Successor v l = (v, l)
newtype LGraph v l = LGraph (HashMap v (HashSet (Successor v l)))

type Edge v l = (v, l, v)

empty :: LGraph v l
empty = LGraph HashMap.empty

edges :: LGraph v l -> [Edge v l]
edges (LGraph gr) = HashMap.foldlWithKey' vEdges [] gr
  where
    vEdges es v₁ sucs =
        HashSet.foldl' (\es' (v₂, l) -> (v₁, l, v₂) : es') [] sucs ++ es

addEdge :: (Eq v, Hashable v, Eq l, Hashable l)
        => Edge v l -> LGraph v l -> LGraph v l
addEdge (v₁, l, v₂) (LGraph oldGr) =
    LGraph $ HashMap.insert v₁ (HashSet.insert (v₂, l) sucs) oldGr'
  where
    oldGr' = addNode v₂ (addNode v₁ oldGr)
    sucs   = oldGr' HashMap.! v₁

    addNode v gr = if HashMap.member v gr then gr
                   else HashMap.insert v HashSet.empty gr

sccs :: (Eq v, Hashable v, Eq l, Hashable l) => LGraph v l -> [[Edge v l]]
sccs = undefined