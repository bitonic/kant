module Language.Bertus.Subst
    ( Subst(..)
    , inst
    , subst
    , (///=)
    , (%%)
    , (%%%)
    , ($$)
    , ($$$)
    , ($*$)
    , abstract
    , abstract'
    , bind
    , pi_
    , pis
    , lam
    , lams
    , lams'
    ) where

import Data.Foldable (Foldable, foldr, foldl)
import Prelude hiding (foldr, foldl)

import Data.Var
import Language.Bertus.Tm

#include "../../impossible.h"

infixl 1 //=

class Subst f where
    (//=) :: f a -> (Head a -> Tm b) -> f b

instance Subst Tm where
    Type            //= _ = Type
    Lam s           //= f = Lam (s ///= f)
    Bind bi lhs rhs //= f = Bind bi (lhs //= f) (rhs ///= f)
    Pair fs sn      //= f = Pair (fs //= f) (sn //= f)
    Neutr v els     //= f = f v %%% map (//= f) els

instance Subst Elim where
    App t //= f = App (t //= f)
    Fst   //= _ = Fst
    Snd   //= _ = Snd

inst :: Subst f => f (Var a v) -> Tm v -> f v
inst s t =
    s //= \v ->
    case v of
        Var  (B _ ) _  -> t
        Var  (F v') tw -> var v' tw
        Meta mv        -> metavar mv

subst :: (Eq v, Subst f) => Head v -> Tm v -> f v -> f v
subst v t u = u //= \v' -> if v == v' then t else Neutr v' []

nestHead :: (Head t -> Tm v) -> Head (Var a t) -> Tm (Var a v)
nestHead _ (Var  (B x) tw) = var (B x) tw
nestHead f (Var  (F v) tw) = f (Var v tw) //= (head_ . nest)
nestHead _ (Meta mv      ) = metavar mv

(///=) :: Subst f => f (Var a t) -> (Head t -> Tm v) -> f (Var a v)
t ///= f = t //= nestHead f

(%%) :: Tm v -> Elim v -> Tm v
Pair t _    %% Fst   = t
Pair _ u    %% Snd   = u
Lam s       %% App t = inst s t
Neutr v els %% el    = Neutr v (els ++ [el])
_           %% _     = IMPOSSIBLE("Bad elimination")

(%%%) :: Tm v -> [Elim v] -> Tm v
(%%%) = foldl (%%)

($$) :: Tm v -> Tm v -> Tm v
t $$ u = t %% App u

($$$) :: Foldable t => Tm v -> t (Tm v) -> Tm v
($$$) = foldl ($$)

($*$) :: (Functor t, Foldable t) => Tm v -> t (v, Tm v) -> Tm v
t $*$ tele = t $$$ fmap (var' . fst) tele

abstract :: (Eq v, Subst f) => a -> v -> Twin -> f v -> f (Var a v)
abstract x nom tw t =
    t //= \v ->
    head_ $ case v of
                Var nom' _ | nom == nom' -> Var (B x) tw
                Var nom' tw'             -> Var (F nom') tw'
                Meta mv                  -> Meta mv

abstract' :: (Eq v, Subst f) => a -> v -> f v -> f (Var a v)
abstract' x nom t = abstract x nom Only t

bind :: Eq v => Bind -> Name -> v -> Ty v -> Ty v -> Ty v
bind bi nom v lhs rhs = Bind bi lhs (abstract' nom v rhs)

pi_ :: Eq v => Name -> v -> Ty v -> Ty v -> Ty v
pi_ = bind Pi

pis :: (Foldable t, Eq v) => t (Name, v, Ty v) -> Ty v -> Ty v
pis xs ty = foldr (\(x, nom, ty') -> pi_ x nom ty') ty xs

lam :: Eq v => Name -> v -> Tm v -> Tm v
lam nom v t = Lam (abstract' nom v t)

lams :: (Foldable t, Eq v) => t (Name, v) -> Tm v -> Tm v
lams xs t = foldr (uncurry lam) t xs

lams' :: (Foldable t, Eq v) => t (Name, v, Ty v) -> Tm v -> Tm v
lams' xs t = foldr (\(nom, v, _) -> lam nom v) t xs

