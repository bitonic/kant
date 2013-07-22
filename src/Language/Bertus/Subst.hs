module Language.Bertus.Subst
    ( Subst(..)
    , inst
    , subst
    , (///=)
    , (%%)
    , (%%%)
    , ($$)
    , ($$$)
    , abstract
    , abstract'
    ) where

import Data.Var
import Language.Bertus.Tm

#include "../../impossible.h"

infixl 1 //=

class Subst f where
    (//=) :: f a -> (Head a -> Tm b) -> f b

instance Subst Tm where
    Canon t         //= f = Canon (t //= f)
    Neutr v els     //= f = f v %%% map (//= f) els

instance Subst Canon where
    Type            //= _ = Type
    Lam s           //= f = Lam (s ///= f)
    Bind bi lhs rhs //= f = Bind bi (lhs //= f) (rhs ///= f)
    Pair fs sn      //= f = Pair (fs //= f) (sn //= f)

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

nest :: (Head t -> Tm v) -> Head (Var a t) -> Tm (Var a v)
nest _ (Var  (B x) tw) = var (B x) tw
nest f (Var  (F v) tw) = f (Var v tw) //= (head_ . fmap F)
nest _ (Meta mv      ) = metavar mv

(///=) :: Subst f => f (Var a t) -> (Head t -> Tm v) -> f (Var a v)
t ///= f = t //= nest f

(%%) :: Tm v -> Elim v -> Tm v
Canon (Pair t _) %% Fst   = t
Canon (Pair _ u) %% Snd   = u
Canon (Lam s   ) %% App t = inst s t
Neutr v els      %% el    = Neutr v (els ++ [el])
_                %% _     = IMPOSSIBLE("Bad elimination")

(%%%) :: Tm v -> [Elim v] -> Tm v
(%%%) = foldl (%%)

($$) :: Tm v -> Tm v -> Tm v
t $$ u = t %% App u

($$$) :: Tm v -> [Tm v] -> Tm v
($$$) = foldl ($$)

abstract :: (Eq v, Subst f) => v -> Twin -> f v -> f (Var v v)
abstract nom tw t =
    t //= \v ->
    head_ $ case v of
                Var nom' _ | nom == nom' -> Var (B nom') tw
                Var nom' tw'             -> Var (F nom') tw'
                Meta mv                  -> Meta mv

abstract' :: (Eq v, Subst f) => v -> f v -> f (Var v v)
abstract' nom t = abstract nom Only t
