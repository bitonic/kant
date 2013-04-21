{-# LANGUAGE PatternGuards #-}
-- | A graph with labelled edges, taken from
--
--     /Structuring Depth-First Search Algorithms in Haskell/,
--     by David King and John Launchbury.
module Data.LGraph
    ( Graph
    , Edge
    , empty
    , build
    , edges
    , vertices
    , addEdge
    , transpose
    , Tree(..)
    , Forest
    , dfs
    , dff
    , scc
    , scc'
    , SCC(..)
    ) where

import           Control.Monad.ST
import           Data.List (foldl')

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import           Data.HashTable.ST.Basic (HashTable)
import qualified Data.HashTable.ST.Basic as HashTable
import           Data.Hashable (Hashable(..))

newtype Graph v l = Graph {unGraph :: HashMap v (HashMap v l)}

type Edge v l = (v, l, v)

empty :: Graph v l
empty = Graph HashMap.empty

build :: (Eq v, Hashable v, Ord l, Hashable l) => [Edge v l] -> Graph v l
build = foldl' (flip addEdge) empty

edges :: Graph v l -> [Edge v l]
edges (Graph gr) = HashMap.foldlWithKey' vEdges [] gr
  where
    vEdges es v₁ sucs =
        HashMap.foldlWithKey' (\es' v₂ l -> (v₁, l, v₂) : es') [] sucs ++ es

vertices :: Graph v l -> [v]
vertices (Graph gr) = HashMap.keys gr

addEdge :: (Eq v, Hashable v, Ord l, Hashable l) => Edge v l -> Graph v l -> Graph v l
addEdge (v₁, l, v₂) (Graph oldGr) = Graph (HashMap.insert v₁ sucs' oldGr')
  where
    oldGr' = addNode v₂ (addNode v₁ oldGr)
    sucs   = oldGr' HashMap.! v₁
    sucs'  = case HashMap.lookup v₂ sucs of
                 Nothing          -> HashMap.insert v₂ l sucs
                 Just l' | l > l' -> HashMap.insert v₂ l sucs
                 _                -> sucs

    addNode v gr = if HashMap.member v gr then gr
                   else HashMap.insert v HashMap.empty gr

reverseG :: Graph v l -> [Edge v l]
reverseG gr = [(v₂, l, v₁) | (v₁, l, v₂) <- edges gr]

transpose :: (Eq v, Hashable v, Ord l, Hashable l) => Graph v l -> Graph v l
transpose = build . reverseG

data Tree v l = Node {nodeV :: v, nodeTs :: [(l, Tree v l)]}
type Forest v l = [Tree v l]

dfs :: (Eq v, Hashable v, Ord l, Hashable l) => Graph v l -> [v] -> Forest v l
dfs g vs = prune (map (generate g) vs)

dff :: (Eq v, Hashable v, Ord l, Hashable l) => Graph v l -> Forest v l
dff gr = dfs gr (vertices gr)

scc :: (Eq v, Hashable v, Ord l, Hashable l) => Graph v l -> Forest v l
scc gr = dfs gr (reverse (postOrd (transpose gr)))

postOrd :: (Eq v, Hashable v, Ord l, Hashable l) => Graph v l -> [v]
postOrd = concatMap postorder . dff
  where
    postorder (Node v ts) = postorderF ts ++ [v]
    postorderF = concatMap (postorder . snd)

generate :: (Eq v, Hashable v, Ord l, Hashable l) => Graph v l -> v -> Tree v l
generate (Graph gr) v₁ = Node v₁ (HashMap.foldrWithKey trees [] (gr HashMap.! v₁))
  where
    trees v₂ l ts = (l, generate (Graph gr) v₂) : ts

type Set s v = HashTable s v ()

prune :: (Eq v, Hashable v) => Forest v l -> Forest v l
prune ts = runST $ do m <- HashTable.new; chopTop m ts

chop :: (Eq v, Hashable v)
     => Set s v
     -> (a -> v) -> (a -> [(l, Tree v l)]) -> (a -> [(l, Tree v l)] -> a)
     -> [a] -> ST s [a]
chop _ _ _ _ [] = return []
chop m getV getTs putTs (n : us) =
    do let v = getV n
       visited <- HashTable.lookup m v
       case visited of
           Nothing -> chop m getV getTs putTs us
           Just () -> do HashTable.insert m v ()
                         as <- chopRec m (getTs n)
                         bs <- chop m getV getTs putTs us
                         return (putTs n as : bs)

chopTop :: (Eq v, Hashable v) => Set s v -> Forest v l -> ST s (Forest v l)
chopTop m = chop m nodeV nodeTs (\n ts -> n{nodeTs = ts})

chopRec :: (Eq v, Hashable v) => Set s v -> [(l, Tree v l)] -> ST s [(l, Tree v l)]
chopRec m = chop m (nodeV . snd) (nodeTs . snd) (\(l, n) ts -> (l, n{nodeTs = ts}))

data SCC v l = Acyclic v | Cyclic [Edge v l]

scc' :: (Eq v, Hashable v, Hashable l, Ord l) => Graph v l -> [SCC v l]
scc' gr = map decode (scc gr)
  where
    decode (Node v []) | Just l <- mentionsItself v = Cyclic [(v, l, v)]
                       | otherwise                  = Acyclic v
    decode ts          = Cyclic (decode' ts )

    decode' (Node v₁ ts) =
        [(v₁, l, v₂) | (l, Node v₂ _) <- ts] ++ concatMap (decode' . snd) ts

    mentionsItself v = HashMap.lookup v (unGraph gr HashMap.! v)

