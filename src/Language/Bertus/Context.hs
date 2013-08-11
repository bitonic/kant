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
    , Context(..)
    , ParamBwdEnd(..)
    , ParamBwd
    , ContextBwd
    , nestCtxBwd
    , lookupCtxBwd
    , ParamList(..)
    , ContextList
    , insertCtxList
    , lookupCtxList
    , toCtxBwd
    , wrapProb
      -- views
    , EqnFR(..)
    , eqnFR
    , frEqn
    , EqnFF(..)
    , eqnFF
    , ffEqn
    , ffFr
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

instance Ord v => Occurs (Decl v) where
    type OccursVar (Decl v) = v

    occurrence _  Hole     = Nothing
    occurrence vs (Defn t) = occurrence vs t

    frees Hole     = mempty
    frees (Defn t) = frees t

data Eqn v = Eqn (Ty v) (Tm v) (Ty v) (Ty v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Subst Eqn where
    Eqn ty1 t1 ty2 t2 //= f =
        Eqn (ty1 //= f) (t1 //= f) (ty2 //= f) (t2 //= f)

instance Ord v => Occurs (Eqn v) where
    type OccursVar (Eqn v) = v
    occurrence vs (Eqn ty1 t1 ty2 t2) = occurrence vs [ty1, t1, ty2, t2]
    frees (Eqn ty1 t1 ty2 t2) =
        frees ty1 <> frees t1 <> frees ty2 <> frees t2

data Problem v = Unify (Eqn v) | All (Param v) (Scope Problem v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Subst Problem where
    Unify eqn    //= f = Unify (eqn //= f)
    All par prob //= f = All (par //= f) (prob ///= f)

instance Ord v => Occurs (Problem v) where
    type OccursVar (Problem v) = v

    occurrence vs (Unify eqn) =
        occurrence vs eqn
    occurrence vs (All par prob) =
        occurrence vs par <> occurrence (nestVarOrMetas vs) prob

    frees (Unify eqn)    = frees eqn
    frees (All par prob) = frees par <> pullVarOrMetas (frees prob)

data Param v = Param (Ty v) | Twins (Ty v) (Ty v)
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Data, Typeable)

instance Subst Param where
    Param ty      //= f = Param (ty //= f)
    Twins ty1 ty2 //= f = Twins (ty1 //= f) (ty2 //= f)

instance Ord v => Occurs (Param v) where
    type OccursVar (Param v) = v

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

instance Ord v => Occurs (Entry v) where
    type OccursVar (Entry v) = v

    occurrence vs (Entry _ ty decl) = occurrence vs ty <> occurrence vs decl
    occurrence vs (Prob _ prob _)   = occurrence vs prob

    frees (Entry _ ty decl) = frees ty <> frees decl
    frees (Prob _ prob _  ) = frees prob

type Subs v = [(Meta, Tm v)]

type ContextL v = Bwd (Entry v)
type ContextR v = [Either (Subs v) (Entry v)]

data Context pars v = Context
    { ctxLeft   :: ContextL v
    , ctxRight  :: ContextR v
    , ctxParams :: pars v
    }

newtype ParamBwdEnd v = ParamBwdEnd (v -> Maybe (Param v))
type ParamBwd = BwdTele Param ParamBwdEnd Name
type ContextBwd = Context ParamBwd

nestCtxBwd :: Param v -> ContextBwd v -> ContextBwd (Var Name v)
nestCtxBwd par (Context le ri pars) =
    Context (fmap nest le) (fmap (fmap (second nest) +++ fmap F) ri)
            (pars :<< par)

lookupCtxBwd :: v -> ContextBwd v -> Maybe (Param v)
lookupCtxBwd v0 (Context _ _ pars) = go pars v0
  where
    go :: ParamBwd v -> v -> Maybe (Param v)
    go (BT0 (ParamBwdEnd f)) v     = f v
    go (bw :<< _)            (F v) = fmap nest (go bw v)
    go (_  :<< t)            (B _) = Just (nest t)

newtype ParamList k v = ParamList {unParamList :: [(k, Param v)]}
type ContextList a = Context (ParamList a)

-- TODO is this right?  can I discard the `k's?
instance Ord v => Occurs (ParamList k v) where
    type OccursVar (ParamList k v) = OccursVar (Param v)
    occurrence vs = occurrence vs . map snd . unParamList
    frees = frees . map snd . unParamList

insertCtxList :: Ord a => a -> Param v -> ContextList a v -> ContextList a v
insertCtxList v par (Context le ri (ParamList pars)) =
    Context le ri (ParamList ((v, par) : pars))

lookupCtxList :: Ord a => a -> ContextList a v -> Maybe (Param v)
lookupCtxList v (Context _ _ (ParamList pars)) = lookup v pars

-- toCtxBwd :: Ord v => ContextList v v -> ContextBwd v
toCtxBwd :: Eq v => ParamList v v -> ParamBwd v
toCtxBwd (ParamList pars) = BT0 (ParamBwdEnd (`lookup` pars))

wrapProb :: Eq v => [(v, Param v)] -> Problem v -> Problem v
wrapProb []                prob = prob
wrapProb ((v, par) : pars) prob = All par $
                                  abstract' mempty v (wrapProb pars prob)


---- Views


data EqnFR v = EqnFR (Ty v) Meta [Elim v] (Ty v) (Tm v)

instance Ord v => Occurs (EqnFR v) where
    type OccursVar (EqnFR v) = v
    occurrence vs = occurrence vs . frEqn
    frees = frees . frEqn

eqnFR :: Eqn v -> Maybe (EqnFR v)
eqnFR (Eqn ty1 (Neutr (Meta mv1) els1) ty2 t2) =
    Just (EqnFR ty1 mv1 els1 ty2 t2)
eqnFR _ =
    Nothing

frEqn :: EqnFR v -> Eqn v
frEqn (EqnFR ty1 mv1 els1 ty2 t2) = Eqn ty1 (Neutr (Meta mv1) els1) ty2 t2

data EqnFF v = EqnFF (Ty v) Meta [Elim v] (Ty v) Meta [Elim v]

instance Ord v => Occurs (EqnFF v) where
    type OccursVar (EqnFF v) = v
    occurrence vs = occurrence vs . ffEqn
    frees = frees . ffEqn

eqnFF :: Eqn v -> Maybe (EqnFF v)
eqnFF (Eqn ty1 (Neutr (Meta mv1) els1) ty2 (Neutr (Meta mv2) els2)) =
    Just (EqnFF ty1 mv1 els1 ty2 mv2 els2)
eqnFF _ =
    Nothing

ffEqn :: EqnFF v -> Eqn v
ffEqn (EqnFF ty1 mv1 els1 ty2 mv2 els2) =
    Eqn ty1 (Neutr (Meta mv1) els1) ty2 (Neutr (Meta mv2) els2)

ffFr :: EqnFF v -> EqnFR v
ffFr (EqnFF ty1 mv1 els1 ty2 mv2 els2) =
    EqnFR ty1 mv1 els1 ty2 (Neutr (Meta mv2) els2)


-- Sym

class Sym eqn where
    sym :: eqn -> eqn

instance Sym (Eqn v) where
    sym (Eqn ty1 t1 ty2 t2) = Eqn ty2 t2 ty1 t1

instance Sym (EqnFF v) where
    sym (EqnFF ty1 mv1 els1 ty2 mv2 els2) = EqnFF ty2 mv2 els2 ty1 mv1 els1

