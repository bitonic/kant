-- TODO replace HashMap.! with IMPOSSIBLE
module Data.Disjoint
    ( Disjoint(..)
    , empty
    , newSet
    , find
    , children
    , union
    ) where

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import           Data.Hashable (Hashable)

#include "../impossible.h"

data Disjoint a = Disjoint
    { disPars  :: HashMap a a
    , disRanks :: HashMap a Int
    , disChis  :: HashMap a (HashSet a)
    }

empty :: Disjoint a
empty = Disjoint { disPars  = HashMap.empty
                 , disRanks = HashMap.empty
                 , disChis  = HashMap.empty }

newSet :: (Eq a, Hashable a) => a -> Disjoint a -> Disjoint a
newSet x dis@Disjoint{disPars = pars, disRanks = ranks, disChis = chis} =
    case HashMap.lookup x pars of
        Nothing -> dis{ disPars  = HashMap.insert x x pars
                      , disRanks = HashMap.insert x 0 ranks
                      , disChis  = HashMap.insert x (HashSet.singleton x) chis }
        Just _  -> IMPOSSIBLE("element already present")

find :: (Eq a, Hashable a) => a -> Disjoint a -> (a, Disjoint a)
find x' dis = (y, dis{disPars = pars'})
  where
    go x pars =
        case pars HashMap.! x of
            par | par /= x -> go par (HashMap.insert x par pars)
            par -> (par, pars)
    (y, pars') = go x' (disPars dis)

children :: (Eq a, Hashable a) => a -> Disjoint a -> (HashSet a, Disjoint a)
children x dis@Disjoint{disChis = chis} = (chis HashMap.! par, dis')
  where (par, dis') = find x dis

rank :: (Eq a, Hashable a) => a -> Disjoint a -> Int
rank x Disjoint{disRanks = ranks} = ranks HashMap.! x

union :: (Eq a, Hashable a) => a -> a -> Disjoint a -> Disjoint a
union x y dis₁ | xrr < yrr = changePar xr yr dis₃
               | xrr > yrr = changePar yr xr dis₃
               | otherwise = changePar yr xr (changeRank xr (xrr + 1) dis₃)
  where
    (xr, dis₂) = find x dis₁
    (yr, dis₃) = find y dis₂
    xrr        = rank xr dis₃
    yrr        = rank yr dis₃

    changePar z par dis@Disjoint{disPars = pars, disChis = chis} =
        let zchis   = chis HashMap.! z
            parchis = chis HashMap.! par
            chis'   = HashMap.delete z chis
        in dis{ disPars = HashMap.insert z par pars
              , disChis = HashMap.insert par (HashSet.union zchis parchis) chis' }
    changeRank z r dis@Disjoint{disRanks = ranks} =
        dis{disRanks = HashMap.insert z r ranks}
