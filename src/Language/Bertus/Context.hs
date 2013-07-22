module Language.Bertus.Context where

import Control.Arrow ((+++), second)
import Data.Data (Data, Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Control.Monad.Fresh
import Data.Bwd
import Language.Bertus.Subst
import Language.Bertus.Tm
import Language.Bertus.Tele


data Decl v = Hole | Defn (Tm v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Subst Decl where
    Hole   //= _ = Hole
    Defn t //= f = Defn (t //= f)

data Eqn v = Eqn (Ty v) (Tm v) (Ty v) (Ty v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Subst Eqn where
    Eqn ty1 t1 ty2 t2 //= f =
        Eqn (ty1 //= f) (t1 //= f) (ty2 //= f) (t2 //= f)

data Problem v = Unify (Eqn v) | All (Param v) (Scope Problem v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Subst Problem where
    Unify eqn    //= f = Unify (eqn //= f)
    All par prob //= f = All (par //= f) (prob ///= f)

data Param v = Param (Ty v) | Twins (Ty v) (Ty v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Subst Param where
    Param ty      //= f = Param (ty //= f)
    Twins ty1 ty2 //= f = Twins (ty1 //= f) (ty2 //= f)

newtype ProbId = ProbId Ref
    deriving (Eq, Ord, Show, Data, Typeable)

data ProblemState = Blocked | Active | Pending [ProbId] | Solved | Failed
    deriving (Eq, Ord, Show, Data, Typeable)

data Entry v
    = Entry Meta (Ty v) (Decl v)
    | Prob ProbId (Problem v) ProblemState
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Subst Entry where
    Entry mv ty decl        //= f = Entry mv (ty //= f) (decl //= f)
    Prob pid prob probstate //= f = Prob pid (prob //= f) probstate

type Subs v = [(Meta, Tm v)]

type ContextL v = Bwd (Entry v)
type ContextR v = [Either (Subs v) (Entry v)]

data Context v = Context
    { ctxLeft   :: ContextL v
    , ctxRight  :: ContextR v
    , ctxParams :: BwdTele Param Proxy Name v
    }

nestCtx :: Param v -> Context v -> Context (Var Name v)
nestCtx par (Context le ri pars) =
    Context (fmap (fmap F) le) (fmap (fmap (second (fmap F)) +++ fmap F) ri)
            (pars :<< par)
