module Kant.Binder (Binder(..)) where

data Binder n = Name n | Wild
    deriving (Show, Eq)
