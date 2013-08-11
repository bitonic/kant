module Language.Bertus.Unify where

import Data.Data (Typeable, Data)
import Data.Foldable (Foldable, foldMap)
import Data.Maybe (isNothing)
import Data.Monoid (mempty, mconcat)

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Bwd
import Language.Bertus.Check
import Language.Bertus.Common
import Language.Bertus.Context
import Language.Bertus.Monad
import Language.Bertus.Occurs
import Language.Bertus.Subst
import Language.Bertus.Tele
import Language.Bertus.Tm

toListMap :: Foldable t => (a -> b) -> t a -> [b]
toListMap f = foldMap (return . f)

newtype FreshVar = FV (Ref, Name)
    deriving (Eq, Ord, Show, Data, Typeable)

type TmFV      = Tm FreshVar
type TyFV      = Ty FreshVar
type ElimFV    = Elim FreshVar
type DeclFV    = Decl FreshVar
type EqnFV     = Eqn FreshVar
type EqnFFFV   = EqnFF FreshVar
type EqnFRFV   = EqnFR FreshVar
type ProblemFV = Problem FreshVar
type ParamFV   = Param FreshVar
type EntryFV   = Entry FreshVar
type ContextFV = ContextList FreshVar FreshVar
type SubsFV    = Subs FreshVar
type BMonadFVT = BMonadListT FreshVar

freshVar :: Monad m => Name -> BMonadFVT m FreshVar
freshVar n = FV . (, n) <$> fresh

freshVar' :: Monad m => BMonadFVT m FreshVar
freshVar' = freshVar mempty

freshMeta :: Monad m => BMonadFVT m Meta
freshMeta = meta <$> fresh

unbind :: Monad m => Scope Tm FreshVar -> BMonadFVT m (FreshVar, TmFV)
unbind t = do v <- freshVar (boundName t)
              return (v, inst t (var' v))

unify :: Monad m => ProbId -> EqnFV -> BMonadFVT m ()
unify pid eqn@(Eqn (Bind Pi dom1 cod1) t1 (Bind Pi dom2 cod2) t2) =
    simplify pid (Unify eqn)
             [ Unify (Eqn Type dom1 Type dom2)
             , All (Twins dom1 dom2) (Unify twinsEqn) ]
  where
    (xL, xR) = (var dummy TwinL, var dummy TwinR)
    twinsEqn = Eqn (nest cod1 `inst` xL) (nest t1 $$ xL)
                   (nest cod2 `inst` xR) (nest t2 $$ xR)
unify pid eqn@(Eqn (Bind Sig fsty1 snty1) t1 (Bind Sig fsty2 snty2) t2) =
    simplify pid (Unify eqn)
             [ Unify (Eqn fsty1 fs1 fsty2 fs2)
             , Unify (Eqn (snty1 `inst` fs1) sn1 (snty2 `inst` fs2) sn2) ]
  where
    (fs1, sn1) = (t1 %% Fst, t1 %% Snd)
    (fs2, sn2) = (t2 %% Fst, t2 %% Snd)
unify pid (eqnFF -> Just ff) =
    tryPrune pid (ffFr ff) (tryPrune pid (ffFr ff) (flexFlex pid ff))
unify pid (eqnFR -> Just fr) =
    tryPrune pid fr (flexRigid [] pid fr)
unify pid eqn@(Eqn _ _ _ (Neutr (Meta _) _)) =
    unify pid (sym eqn)
unify pid eqn =
    rigidRigid eqn >>= simplify pid (Unify eqn) . map Unify

rigidRigid :: Monad m => EqnFV -> BMonadFVT m [EqnFV]
rigidRigid (Eqn Type Type Type Type) = return []
rigidRigid (Eqn Type (Bind bi1 dom1 cod1) Type (Bind bi2 dom2 cod2))
    | bi1 == bi2 =
    return [ Eqn Type dom1 Type dom2
           , Eqn (dom1 --> Type) (Lam cod1) (dom2 --> Type) (Lam cod2) ]
-- TODO throwing away types
rigidRigid (Eqn _ (Neutr (Var v1 tw1) els1) _ (Neutr (Var v2 tw2) els2))
    | v1 == v2 =
    do tyv1 <- lookupVar lookupCtxList v1 tw1
       tyv2 <- lookupVar lookupCtxList v2 tw2
       (Eqn Type tyv1 Type tyv2 :) <$>
           matchSpine tyv1 (var v1 tw1) els1 tyv2 (var v2 tw2) els2
rigidRigid _ =
    throwError "rigidRigid mismatch"

matchSpine :: Monad m
           => TyFV -> TmFV -> [ElimFV] -> TyFV -> TmFV -> [ElimFV]
           -> BMonadFVT m [EqnFV]
matchSpine _ _ [] _ _ [] =
    return []
matchSpine (Bind Pi dom1 cod1) t1 (App u1 : els1)
           (Bind Pi dom2 cod2) t2 (App u2 : els2) =
    (Eqn dom1 u1 dom2 u2 :) <$>
    matchSpine (cod1 `inst` u1) (t1 $$ u1) els1
               (cod2 `inst` u2) (t2 $$ u2) els2
matchSpine (Bind Sig fsty1 _) t1 (Fst : els1)
           (Bind Sig fsty2 _) t2 (Fst : els2) =
    matchSpine fsty1 (t1 %% Fst) els1 fsty2 (t2 %% Fst) els2
matchSpine (Bind Sig _ snty1) t1 (Snd : els1)
           (Bind Sig _ snty2) t2 (Snd : els2) =
    matchSpine (snty1 `inst` fs1) sn1 els1 (snty2 `inst` fs2) sn2 els2
  where
    (fs1, sn1) = (t1 %% Fst, t1 %% Snd)
    (fs2, sn2) = (t2 %% Fst, t2 %% Snd)
matchSpine _ _ _ _ _ _ = throwError "spine mismatch"

flexRigid :: Monad m => [EntryFV] -> ProbId -> EqnFRFV -> BMonadFVT m ()
flexRigid depends pid fr@(EqnFR _ mv1 _ _ _) =
    do pars <- gets ctxParams
       entry <- popL
       case entry of
           Entry mv2 mv2ty Hole
               | mv1 == mv2 && mv1 `Set.member` fmvs depends ->
               do pushL entry
                  mapM_ pushL depends
                  block pid (frEqn fr)
               | mv1 == mv2 ->
               do mapM_ pushL depends
                  tryInvert pid fr mv2ty (block pid (frEqn fr) *> pushL entry)
               | mv2 `Set.member` fmvs (pars, depends, fr) ->
               flexRigid (entry : depends) pid fr
           _ ->
               do pushR (Right entry)
                  flexRigid depends pid fr

flexFlex :: Monad m => ProbId -> EqnFFFV -> BMonadFVT m ()
flexFlex pid ff@(EqnFF _ mv1 els1 _ mv2 els2) =
    do pars <- gets ctxParams
       entry <- popL
       case entry of
           Entry mv3 mv3ty Hole
               | mv3 == mv1 && mv3 == mv1 ->
               do block pid (ffEqn ff)
                  tryIntersect mv1 mv3ty els1 els2
               | mv3 == mv1 ->
               tryInvert pid fr mv3ty (flexRigid [entry] pid frSym)
               | mv3 == mv2 ->
               tryInvert pid frSym mv3ty (flexRigid [entry] pid fr)
               | mv3 `Set.member` fmvs (pars, ff) ->
               do pushL entry
                  block pid (ffEqn ff)
           _ ->
               do pushR (Right entry)
                  flexFlex pid ff
  where
    fr = ffFr ff
    frSym = ffFr (sym ff)

tryInvert :: Monad m
          => ProbId -> EqnFRFV -> TyFV -> BMonadFVT m () -> BMonadFVT m ()
tryInvert pid fr@(EqnFR _ mv1 els1 _ t2) ty1 m =
    do t1m <- invert mv1 ty1 els1 t2
       case t1m of
           Nothing -> m
           Just t1 -> active pid (frEqn fr) *> define [] mv1 ty1 t1

invert :: Monad m
       => Meta -> TyFV -> [ElimFV] -> TmFV -> BMonadFVT m (Maybe TmFV)
invert mv1 ty1 els1 t2 =
    do when (isStrongRigid o) (throwError "occurrence")
       case toVars els1 of
           Just vs | Nothing <- o, linearOn t2 vs ->
               do let t = lams' vs t2
                  b <- localParams (const (BT0 (ParamBwdEnd (const Nothing))))
                                   (typecheck ty1 t)
                  return (if b then Just t else Nothing)
           _ ->
               return Nothing
  where
    o = occurrence (Set.singleton (Left mv1)) t2

tryIntersect :: Monad m
             => Meta -> TyFV -> [ElimFV] -> [ElimFV] -> BMonadFVT m ()
tryIntersect mv ty els1 els2 =
    case (toVars els1, toVars els2) of
        (Just vs1, Just vs2) ->
            do m <- intersect B0 B0 ty vs1 vs2
               case m of
                   Just (ty', f) -> hole [] ty' (define [] mv ty . f)
                   Nothing       -> pushL (Entry mv ty Hole)
        _ ->
            pushL (Entry mv ty Hole)

intersect :: Monad m
          => Bwd (FreshVar, TyFV) -> Bwd (FreshVar, TyFV)
          -> TyFV -> [FreshVar] -> [FreshVar]
          -> BMonadFVT m (Maybe (TyFV, TmFV -> TmFV))
intersect tys1 tys2 ty [] [] =
    return $
    if fvs ty `Set.isSubsetOf` vars tys1
    then Just (pis' tys2 ty, \mv -> lams' (fmap fst tys1) (mv $*$ tys2))
    else Nothing
intersect tys1 tys2 (Bind Pi dom cod) (v1 : vs1) (v2 : vs2) =
    do v <- freshVar (boundName cod)
       let tys2' = if v1 == v2 then tys2 :< (v, dom) else tys2
       intersect (tys1 :< (v, dom)) tys2' (cod `inst` var' v) vs1 vs2
intersect _ _ _ _ _ =
    error "intersect: ill-typed!"

simplify :: Monad m
         => ProbId -> ProblemFV -> [ProblemFV] -> BMonadFVT m ()
simplify pid prob probs = go probs []
  where
    go :: Monad m => [ProblemFV] -> [ProbId] -> BMonadFVT m ()
    go [] pids =
        pendingSolve pid prob pids
    go (prob' : probs') pids =
        do pid' <- probId <$> fresh
           ParamList pars <- gets ctxParams
           pushL (Prob pid' (wrapProb pars prob') Active)
           go probs' (pid' : pids) <* goL

putProb :: Monad m => ProbId -> ProblemFV -> ProblemState -> BMonadFVT m ()
putProb pid prob pst = do ParamList pars <- gets ctxParams
                          pushR (Right (Prob pid (wrapProb pars prob) pst))

pendingSolve :: Monad m => ProbId -> ProblemFV -> [ProbId] -> BMonadFVT m ()
pendingSolve pid prob []   = do localParams toCtxBwd (checkProb Solved prob)
                                putProb pid prob Solved
pendingSolve pid prob pids = putProb pid prob (Pending pids)

tryPrune :: Monad m => ProbId -> EqnFRFV -> BMonadFVT m () -> BMonadFVT m ()
tryPrune pid fr@(EqnFR _ _ els1 _ t2) m =
    do ParamList pars <- gets ctxParams
       pruneds <- prune (vars pars `Set.intersection` fvs els1) t2
       case pruneds of
           pruned : _ -> active pid (frEqn fr) *> instantiate pruned
           []         -> m

vars :: Foldable t => t (FreshVar, a) -> Set FreshVar
vars = Set.fromList . toListMap fst

prune :: Monad m
      => Set FreshVar -> TmFV -> BMonadFVT m [(Meta, TyFV, TmFV -> TmFV)]
prune _  Type =
    return []
prune vs (Bind _ lhs rhs) =
    (++) <$> prune vs lhs <*> pruneScope vs rhs
prune vs (Pair fs sn) =
    (++) <$> prune vs fs <*> prune vs sn
prune vs (Lam t) =
    pruneScope vs t
prune vs (Neutr (Var v _) els) =
    if v `Set.member` vs then throwError "pruning error"
    else mconcat <$> mapM pruneElim els
  where
    pruneElim (App t) = prune vs t
    pruneElim _       = return mempty
prune vs (Neutr (Meta mv) els) =
    do ty1 <- lookupMeta mv
       maybe [] (\(ty2, f) -> [(mv, ty2, f)]) <$> pruneSpine B0 B0 vs ty1 els

pruneScope :: Monad m
           => Set FreshVar -> Scope Tm FreshVar
           -> BMonadFVT m [(Meta, TyFV, TmFV -> TmFV)]
pruneScope vs t = prune vs . snd =<< unbind t

pruneSpine :: Monad m
           => Bwd (FreshVar, TyFV) -> Bwd (FreshVar, TyFV) -> Set FreshVar
           -> TyFV -> [ElimFV] -> BMonadFVT m (Maybe (TyFV, TmFV -> TmFV))
pruneSpine unpruned pruned vs (Bind Pi dom cod) (App t : els) =
    if not stuck
    then do v <- freshVar'
            let pruned' = if toPrune then pruned else pruned :< (v, dom)
            pruneSpine (unpruned :< (v, dom)) pruned' vs (cod `inst` var' v) els
    else return Nothing
  where
    -- TODO try to not map over the set
    occ     = occurrence (Set.mapMonotonic Right vs) t
    occ'    = occurrence (vset pruned `Set.difference` vset unpruned) dom
    vset    = Set.fromList . toListMap (Right . fst)
    toPrune = isRigid occ || isRigid occ'
    stuck   = isFlexible occ || (isNothing occ && isFlexible occ') ||
              (not toPrune && not (isVar t))
pruneSpine unpruned pruned _ ty []
    | fvs ty `Set.isSubsetOf` vars pruned, pruned /= unpruned =
        return (Just (pis pruned' ty, \v -> lams unpruned' (v $*$ unpruned)))
  where
    unpruned' = fmap (\(fv@(FV (_, nom)), _)   -> (nom, fv))      unpruned
    pruned'   = fmap (\(fv@(FV (_, nom)), ty') -> (nom, fv, ty')) pruned
pruneSpine _ _ _ _ _ = return Nothing

active, block :: Monad m => ProbId -> EqnFV -> BMonadFVT m ()
active pid eqn = putProb pid (Unify eqn) Active
block  pid eqn = putProb pid (Unify eqn) Blocked

-- TODO passing all these functions around is ugly
instantiate :: Monad m => (Meta, TyFV, TmFV -> TmFV) -> BMonadFVT m ()
instantiate pruned@(mv, ty1, f) =
    do entry <- popL
       case entry of
           Entry mv' ty2 Hole | mv == mv' ->
               hole [] ty1 (\t -> define [] mv' ty2 (f t))
           _ ->
               pushR (Right entry) *> instantiate pruned

hole :: Monad m
     => [(FreshVar, TyFV)] -> TyFV -> (TmFV -> BMonadFVT m a) -> BMonadFVT m a
hole tys ty f =
    do catchError (localParams toCtxBwd (check Type (pis' tys ty)))
                  (const (error "hole"))
       mv <- freshMeta
       pushL (Entry mv (pis' tys ty) Hole)
       f (Neutr (Meta mv) [] $*$ tys) <* goLeft

define :: Monad m
       => [(FreshVar, TyFV)] -> Meta -> TyFV -> TmFV -> BMonadFVT m ()
define tys mv ty0 t0 =
    do localParams toCtxBwd (check ty t) `catchError` const (error "define")
       pushL (Entry mv ty (Defn t))
       pushR (Left [(mv, t)])
       goLeft
  where
    ty = pis' tys ty0
    t  = lams' (map fst tys) t0

goLeft :: Monad m => BMonadFVT m ()
goLeft = popL >>= pushR . Right
