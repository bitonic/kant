{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | A graph with labelled edges and condensing of SCCs, derived from
--
--     /Structuring Depth-First Search Algorithms in Haskell/,
--     by David King and John Launchbury.
-- TODO I can greatly improve the efficiency of this:
--   * Prune vertices of variables that do not appear anymore, preserving the
--     paths.
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
    , inEdges
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
    , scc
    , condense
    , condenseAll
    ) where

import           Control.Monad.ST
import           Data.List (foldl')

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import           Data.HashTable.ST.Basic (HashTable)
import qualified Data.HashTable.ST.Basic as HashTable
import           Data.Hashable (Hashable(..))
#include "../impossible.h"
#include "../containers.h"

newtype Rep v = Rep v deriving (Show, Eq, Hashable)

data Graph v l = Graph
    { grSucs :: HashMap (Rep v) (HashMap (Rep v) l)
    , grReps :: HashMap v (Rep v)
    , grSper :: HashMap (Rep v) (HashSet v)
    } deriving (Show)

type Edge v l = (v, l, v)
type RepEdge v l = (Rep v, l, Rep v)

empty :: Graph v l
empty = Graph HashMap.empty HashMap.empty HashMap.empty

addVertex :: (Eq v, Hashable v) => v -> Graph v l -> (Rep v, Graph v l)
addVertex v gr@Graph{grSucs = sucs, grReps = reps, grSper = sper} =
    case HashMap.lookup v reps of
        Nothing  -> let r = Rep v
                    in (r, gr{ grSucs = HashMap.insert r HashMap.empty sucs
                             , grReps = HashMap.insert v r reps
                             , grSper = HashMap.insert r (HashSet.singleton v) sper })
        Just rep -> (rep, gr)

build :: (Eq v, Hashable v, Ord l) => [Edge v l] -> Graph v l
build = foldl' (flip addEdge) empty

addEdge :: (Eq v, Hashable v, Ord l) => Edge v l -> Graph v l -> Graph v l
addEdge (v₁, l, v₂) gr₁ = gr₃{grSucs = HashMap.insert r₁ r₁sucs' sucs}
  where
    (r₁, gr₂) = addVertex v₁ gr₁
    (r₂, gr₃@Graph{grSucs = sucs}) = addVertex v₂ gr₂
    r₁sucs = HMBANG(r₁, sucs)
    r₁sucs' = case HashMap.lookup r₂ r₁sucs of
                  Just l' | l <= l' -> r₁sucs
                  _ -> HashMap.insert r₂ l r₁sucs

edges :: Graph v l -> [RepEdge v l]
edges = HashMap.foldlWithKey' vEdges [] . grSucs
  where
    vEdges es r₁ sucs =
        HashMap.foldlWithKey' (\es' r₂ l -> (r₁, l, r₂) : es') [] sucs ++ es

-- TODO I'd like this to be more efficient, without doing the edges on a second
-- pass.  We could already make this faster by using ST when collecting the
-- edges.
inEdges :: (Eq v, Hashable v, Ord l, Hashable l)
        => [Rep v] -> Graph v l -> [RepEdge v l]
inEdges rs Graph{grSucs = sucs} = go (HashSet.fromList rs)
  where
    go s =
        HashSet.foldl'
        (\es r₁ -> HashMap.foldlWithKey' (\es' r₂ l -> if HashSet.member r₂ s
                                                       then (r₁, l, r₂) : es'
                                                       else es')
                   [] HMBANG(r₁, sucs) ++ es) [] s

vertices :: Graph v l -> [Rep v]
vertices = HashMap.keys . grSucs

reverseG :: Graph v l -> [RepEdge v l]
reverseG gr = [(v₂, l, v₁) | (v₁, l, v₂) <- edges gr]

transpose :: (Eq v, Hashable v) => Graph v l -> Graph v l
transpose gr = gr{grSucs = repBuild (reverseG gr)}
  where
    repBuild = foldl' (\hm (r₁, l, r₂) ->
                        let r₁sucs = case HashMap.lookup r₁ hm of
                                         Nothing -> HashMap.empty
                                         Just s  -> s
                        in HashMap.insert r₁ (HashMap.insert r₂ l r₁sucs) hm)
               (foldl' (\hm r -> HashMap.insert r HashMap.empty hm)
                       HashMap.empty (vertices gr))

data Tree v l = Node (Rep v) (Forest v l)
type Forest v l = [Tree v l]

dfs :: (Eq v, Hashable v, Ord l) => Graph v l -> [Rep v] -> Forest v l
dfs g vs = prune (map (generate g) vs)

dff :: (Eq v, Hashable v, Ord l) => Graph v l -> Forest v l
dff gr = dfs gr (vertices gr)

postOrd :: (Eq v, Hashable v, Ord l) => Graph v l -> [Rep v]
postOrd = postorderF . dff
  where
    postorder (Node v ts) = postorderF ts ++ [v]
    postorderF = concatMap postorder

generate :: (Eq v, Hashable v, Ord l) => Graph v l -> Rep v -> Tree v l
-- Note that we use a lazy foldr since the trees generated might be infinite.
generate gr@Graph{grSucs = sucs} r₁ =
    Node r₁ (HashMap.foldrWithKey trees [] HMBANG(r₁, sucs))
  where trees r₂ _ ts = generate gr{grSucs = sucs} r₂ : ts

prune :: (Eq v, Hashable v) => Forest v l -> Forest v l
prune ts = runST $ do m <- HashTable.new; chop m ts

chop :: (Eq v, Hashable v) => HashTable s (Rep v) () -> Forest v l -> ST s (Forest v l)
chop _ [] = return []
chop m (Node r ts : us) =
    do visited <- HashTable.lookup m r
       case visited of
           Just () -> chop m us
           Nothing -> do HashTable.insert m r ()
                         as <- chop m ts
                         bs <- chop m us
                         return (Node r as : bs)

scc' :: (Eq v, Hashable v, Ord l, Hashable l) => Graph v l -> Forest v l
scc' gr = dfs gr (reverse (postOrd (transpose gr)))

data SCC v l = Acyclic (Rep v) | Cyclic [Rep v]
    deriving (Show)

scc :: (Eq v, Hashable v, Hashable l, Ord l) => Graph v l -> [SCC v l]
scc gr = map decode (scc' gr)
  where
    decode (Node v []) = if mentionsItself v then Cyclic [v] else Acyclic v
    decode ts          = Cyclic (decode' ts)
    decode' (Node v₁ ts) = v₁ : concatMap decode' ts
    mentionsItself v = HashMap.member v HMBANG(v, grSucs gr)

condense :: (Eq v, Hashable v) => SCC v l -> Graph v l -> Graph v l
condense (Acyclic _) gr = gr
condense (Cyclic []) _ = IMPOSSIBLE("empty Cyclic received")
condense (Cyclic (r : rs)) Graph{grSucs = sucs, grReps = reps, grSper = sper} =
    Graph{ grSucs = HashMap.map replace sucs'
         , grReps = HashSet.foldl' (\hm v -> HashMap.insert v r hm) reps rssper
         , grSper = HashMap.insert r rsper (clean sper) }
  where
    clean   hm = foldl' (flip HashMap.delete) hm rs
    replace hm = foldl' (\hm' r' ->
                          case HashMap.lookup r' hm of
                              Nothing -> hm'
                              Just l  -> HashMap.insert r l (HashMap.delete r' hm'))
                 hm rs

    bang x hm = HMBANG(x, hm)

    rssper = foldl' HashSet.union HashSet.empty (map (`bang` sper) rs)
    rsper  = HashSet.union rssper HMBANG(r, sper)

    sucs'  = clean (HashMap.insert r (clean (bang r sucs)) sucs)

condenseAll :: (Eq v, Hashable v) => [SCC v l] -> Graph v l -> Graph v l
condenseAll ss gr = foldl' (flip condense) gr ss
