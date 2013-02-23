{-# LANGUAGE DeriveFunctor #-}
module Kant.Binder
    ( Binder(..)
    , isBind
    , isWild
    , bindElem
    , binder
    , fromBinder
    , toBinder
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

binder :: b -> (a -> b) -> Binder n a -> b
binder x _ Wild = x
binder _ f (Bind _ x) = f x

fromBinder :: Binder a a -> Maybe a
fromBinder Wild       = Nothing
fromBinder (Bind _ n) = Just n

toBinder :: Maybe a -> Binder a a
toBinder Nothing  = Wild
toBinder (Just x) = Bind x x