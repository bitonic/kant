module Kant.Binder (Binder(..)) where

data Binder n
    = Name n
    | Wildcard
    deriving (Show, Eq)
