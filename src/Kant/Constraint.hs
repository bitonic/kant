module Kant.Constraint
    ( Constr(..)
    , Constrs
    , emptyConstrs
    , addConstr
    , addConstrs
    ) where

import           Data.Foldable (foldrM)

data Constrs a = Constrs

data Constr a = a :<=: a | a :<: a | a :==: a

emptyConstrs :: Constrs a
emptyConstrs = undefined

addConstr :: Ord a => Constr a -> Constrs a -> Maybe (Constrs a)
addConstr = undefined

addConstrs :: Ord a => [Constr a] -> Constrs a -> Maybe (Constrs a)
addConstrs = flip (foldrM addConstr)
