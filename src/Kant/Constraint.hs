module Kant.Constraint
    ( Constr(..)
    , Constrs
    , emptyConstrs
    , addConstr
    , cyclical
    ) where

data Constrs a = Constrs

data Constr a = a :<=: a | a :==: a

emptyConstrs :: Constrs a
emptyConstrs = undefined

addConstr :: Ord a => Constr a -> Constrs a -> Constrs a
addConstr = undefined

cyclical :: Ord a => Constrs a -> Bool
cyclical = undefined
