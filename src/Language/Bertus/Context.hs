module Language.Bertus.Context
    ( Decl(..)
    , Eqn(..)
    , sym
    , Problem(..)
    , Param(..)
    , ProbId
    , probId
    , ProblemState(..)
    , Entry(..)
    , Subs
    , ContextL
    , ContextR
    , Params
    , Context(..)
    , nestCtx
    ) where

import Control.Arrow ((+++), second)
import Data.Data (Data, Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Monoid (mempty, (<>))

import Control.Monad.Fresh
import Data.Bwd
import Language.Bertus.Occurs
import Language.Bertus.Subst
import Language.Bertus.Tele
import Language.Bertus.Tm

data Decl v = Hole | Defn (Tm v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Subst Decl where
    Hole   //= _ = Hole
    Defn t //= f = Defn (t //= f)

instance Occurs Decl where
    occurrence _  Hole     = Nothing
    occurrence vs (Defn t) = occurrence vs t

    frees Hole     = mempty
    frees (Defn t) = frees t

data Eqn v = Eqn (Ty v) (Tm v) (Ty v) (Ty v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

sym :: Eqn v -> Eqn v
sym (Eqn ty1 t1 ty2 t2) = Eqn ty2 t2 ty1 t1

instance Subst Eqn where
    Eqn ty1 t1 ty2 t2 //= f =
        Eqn (ty1 //= f) (t1 //= f) (ty2 //= f) (t2 //= f)

instance Occurs Eqn where
    occurrence vs (Eqn ty1 t1 ty2 t2) = occurrenceList vs [ty1, t1, ty2, t2]
    frees (Eqn ty1 t1 ty2 t2) =
        frees ty1 <> frees t1 <> frees ty2 <> frees t2

data Problem v = Unify (Eqn v) | All (Param v) (Scope Problem v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Subst Problem where
    Unify eqn    //= f = Unify (eqn //= f)
    All par prob //= f = All (par //= f) (prob ///= f)

instance Occurs Problem where
    occurrence vs (Unify eqn) =
        occurrence vs eqn
    occurrence vs (All par prob) =
        occurrence vs par <> occurrenceScope vs prob

    frees (Unify eqn)    = frees eqn
    frees (All par prob) = frees par <> freesScope prob

data Param v = Param (Ty v) | Twins (Ty v) (Ty v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Subst Param where
    Param ty      //= f = Param (ty //= f)
    Twins ty1 ty2 //= f = Twins (ty1 //= f) (ty2 //= f)

instance Occurs Param where
    occurrence vs (Param ty)      = occurrence vs ty
    occurrence vs (Twins tyL tyR) = occurrence vs tyL <> occurrence vs tyR

    frees (Param ty     ) = frees ty
    frees (Twins tyL tyR) = frees tyL <> frees tyR

newtype ProbId = ProbId Ref
    deriving (Eq, Ord, Show, Data, Typeable)

probId :: Ref -> ProbId
probId = ProbId

data ProblemState = Blocked | Active | Pending [ProbId] | Solved | Failed
    deriving (Eq, Ord, Show, Data, Typeable)

data Entry v
    = Entry Meta (Ty v) (Decl v)
    | Prob ProbId (Problem v) ProblemState
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Subst Entry where
    Entry mv ty decl        //= f = Entry mv (ty //= f) (decl //= f)
    Prob pid prob probstate //= f = Prob pid (prob //= f) probstate

instance Occurs Entry where
    occurrence vs (Entry _ ty decl) = occurrence vs ty <> occurrence vs decl
    occurrence vs (Prob _ prob _)   = occurrence vs prob

    frees (Entry _ ty decl) = frees ty <> frees decl
    frees (Prob _ prob _  ) = frees prob

type Subs v = [(Meta, Tm v)]

type ContextL v = Bwd (Entry v)
type ContextR v = [Either (Subs v) (Entry v)]

type Params = BwdTele Param Proxy Name

data Context v = Context
    { ctxLeft   :: ContextL v
    , ctxRight  :: ContextR v
    , ctxParams :: Params v
    }

nestCtx :: Param v -> Context v -> Context (Var Name v)
nestCtx par (Context le ri pars) =
    Context (fmap nest le) (fmap (fmap (second nest) +++ fmap F) ri)
            (pars :<< par)
