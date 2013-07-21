module Language.Bertus.Tele
    ( module Data.Proxy
    , FwdTele(..)
    , BwdTele(..)
    , tailBwd
    , lookBwd
    ) where

import Data.Traversable (Traversable)
import Data.Foldable (Foldable)

import Data.Proxy

import Data.Var
import Language.Bertus.Subst

infixl 5 :>>
data FwdTele f g a v where
    FT0   :: g v -> FwdTele f g a v
    (:>>) :: f v -> FwdTele f g a (Var a v) -> FwdTele f g a v
    deriving (Functor, Foldable, Traversable)

instance (Subst f, Subst g) => Subst (FwdTele f g a) where
    FT0 t     //= f = FT0 (t //= f)
    ty :>> te //= f = (ty //= f) :>> (te ///= f)

infixr 5 :<<
data BwdTele f g a v where
    BT0   :: g v -> BwdTele f g a v
    (:<<) :: BwdTele f g a v -> f v -> BwdTele f g a (Var a v)


tailBwd :: BwdTele f g a (Var a v) -> BwdTele f g a v
tailBwd (bw :<< _) = bw

lookBwd :: Functor f => BwdTele f g a v -> v -> Maybe (f v)
lookBwd (BT0 _)    _     = Nothing
lookBwd (bw :<< _) (F v) = fmap (fmap F) (lookBwd bw v)
lookBwd (_  :<< t) (B _) = Just (fmap F t)
