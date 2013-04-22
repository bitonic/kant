{-# LANGUAGE PatternGuards #-}
-- | A graph with labelled edges, taken from
--
--     /Structuring Depth-First Search Algorithms in Haskell/,
--     by David King and John Launchbury.
module Data.LGraph
    ( -- * Graph type
      Graph
      -- * Construction
    , Edge
    , empty
    , build
    , addEdge
      -- * Edges and vertices
    , edges
    , vertices
      -- * Transformations
    , transpose
      -- * DFS search
    , Tree(Node)
    , Forest
    , dfs
    , dff
      -- * Strongly connected components
    , SCC(..)
    , scc'
    , scc
    ) where

import           Control.Monad.ST
import           Data.List (foldl')

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import           Data.HashTable.ST.Basic (HashTable)
import qualified Data.HashTable.ST.Basic as HashTable
import           Data.Hashable (Hashable(..))

newtype Graph v l = Graph {unGraph :: HashMap v (HashMap v l)}

type Edge v l = (v, l, v)

empty :: Graph v l
empty = Graph HashMap.empty

build :: (Eq v, Hashable v, Ord l, Hashable l) => [Edge v l] -> Graph v l
build = foldl' (flip addEdge) empty

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

edges :: Graph v l -> [Edge v l]
edges (Graph gr) = HashMap.foldlWithKey' vEdges [] gr
  where
    vEdges es v₁ sucs =
        HashMap.foldlWithKey' (\es' v₂ l -> (v₁, l, v₂) : es') [] sucs ++ es

vertices :: Graph v l -> [v]
vertices (Graph gr) = HashMap.keys gr

reverseG :: Graph v l -> [Edge v l]
reverseG gr = [(v₂, l, v₁) | (v₁, l, v₂) <- edges gr]

transpose :: (Eq v, Hashable v, Ord l, Hashable l) => Graph v l -> Graph v l
transpose = build . reverseG

data Tree v l = Node v (Forest v l)
type Forest v l = [Tree v l]

dfs :: (Eq v, Hashable v, Ord l, Hashable l) => Graph v l -> [v] -> Forest v l
dfs g vs = prune (map (generate g) vs)

dff :: (Eq v, Hashable v, Ord l, Hashable l) => Graph v l -> Forest v l
dff gr = dfs gr (vertices gr)

postOrd :: (Eq v, Hashable v, Ord l, Hashable l) => Graph v l -> [v]
postOrd = postorderF . dff
  where
    postorder (Node v ts) = postorderF ts ++ [v]
    postorderF = concatMap postorder

generate :: (Eq v, Hashable v, Ord l, Hashable l) => Graph v l -> v -> Tree v l
-- Note that we use a lazy foldr since the trees generated might be infinite.
generate (Graph gr) v₁ = Node v₁ (HashMap.foldrWithKey trees [] (gr HashMap.! v₁))
  where trees v₂ _ ts = generate (Graph gr) v₂ : ts

prune :: (Eq v, Hashable v) => Forest v l -> Forest v l
prune ts = runST $ do m <- HashTable.new; chop m ts

chop :: (Eq v, Hashable v) => HashTable s v () -> Forest v l -> ST s (Forest v l)
chop _ [] = return []
chop m (Node v ts : us) =
    do visited <- HashTable.lookup m v
       case visited of
           Just () -> chop m us
           Nothing -> do HashTable.insert m v ()
                         as <- chop m ts
                         bs <- chop m us
                         return (Node v as : bs)

scc' :: (Eq v, Hashable v, Ord l, Hashable l) => Graph v l -> Forest v l
scc' gr = dfs gr (reverse (postOrd (transpose gr)))

data SCC v l = Acyclic v | Cyclic [Edge v l]
    deriving (Show)

-- TODO I'd like this to be more efficient, without doing the edges on a second
-- pass.  We could already make this faster by using ST when collecting the
-- edges.
scc :: (Eq v, Hashable v, Hashable l, Ord l) => Graph v l -> [SCC v l]
scc gr = map decode (scc' gr)
  where
    decode (Node v []) | Just l <- mentionsItself v = Cyclic [(v, l, v)]
                       | otherwise                  = Acyclic v
    decode ts          = Cyclic (getEdges (decode' ts HashSet.empty))

    decode' (Node v₁ ts) s = foldl' (flip decode') (HashSet.insert v₁ s) ts

    mentionsItself v = HashMap.lookup v (unGraph gr HashMap.! v)

    getEdges s =
        HashSet.foldl'
        (\es v₁ -> HashMap.foldlWithKey' (\es' v₂ l -> if HashSet.member v₂ s
                                                       then (v₁, l, v₂) : es'
                                                       else es')
                   [] (unGraph gr HashMap.! v₁) ++ es) [] s
