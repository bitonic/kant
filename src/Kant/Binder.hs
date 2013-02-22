{-# LANGUAGE DeriveFunctor #-}
module Kant.Binder
    ( Binder(..)
    , isBind
    , isWild
    , bindElem
    , bind
    ) where

-- | The @n@ is a forgettable name.
data Binder n a
    = Bind n a
    | Wild
    deriving (Show, Functor)

isBind, isWild :: Binder n a -> Bool
isBind (Bind _ _) = True
isBind Wild       = False
isWild = not . isBind

instance Eq a => Eq (Binder n a) where
    Wild     == Wild     = True
    Bind _ a == Bind _ b = a == b
    _        == _        = False

bindElem :: Eq a => a -> [Binder n a] -> Bool
bindElem x bs = not (null ([() | Bind _ x' <- bs, x == x']))

bind :: a -> Binder a a
bind n = Bind n n