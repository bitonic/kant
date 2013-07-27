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

unbind :: Monad m => Scope Tm FreshVar -> BMonadFVT m (FreshVar, TmFV)
unbind t = do v <- freshVar (boundName t)
              return (v, inst t (var' v))

data FREqn = FREqn TyFV Meta [ElimFV] TyFV TmFV

eqnFR :: EqnFV -> Maybe FREqn
eqnFR (Eqn ty1 (Neutr (Meta mv1) els1) ty2 t2) =
    Just (FREqn ty1 mv1 els1 ty2 t2)
eqnFR _ =
    Nothing

frEqn :: FREqn -> EqnFV
frEqn (FREqn ty1 mv1 els1 ty2 t2) = Eqn ty1 (Neutr (Meta mv1) els1) ty2 t2

data FFEqn = FFEqn TyFV Meta [ElimFV] TyFV Meta [ElimFV]

eqnFF :: EqnFV -> Maybe FFEqn
eqnFF (Eqn ty1 (Neutr (Meta mv1) els1) ty2 (Neutr (Meta mv2) els2)) =
    Just (FFEqn ty1 mv1 els1 ty2 mv2 els2)
eqnFF _ =
    Nothing

ffEqn :: FFEqn -> EqnFV
ffEqn (FFEqn ty1 mv1 els1 ty2 mv2 els2) =
    Eqn ty1 (Neutr (Meta mv1) els1) ty2 (Neutr (Meta mv2) els2)

ffFr :: FFEqn -> FREqn
ffFr (FFEqn ty1 mv1 els1 ty2 mv2 els2) =
    FREqn ty1 mv1 els1 ty2 (Neutr (Meta mv2) els2)

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

flexRigid :: Monad m => [EntryFV] -> ProbId -> FREqn -> BMonadFVT m ()
flexRigid depends pid fr@(FREqn _ mv1 _ _ _) =
    do entry <- popL
       case entry of
           Entry mv2 mv2ty Hole
               | mv1 == mv2 && mv1 `Set.member` fmvs depends ->
               do pushL entry
                  mapM_ pushL depends
                  block pid (frEqn fr)
               | mv1 == mv2 ->
               do mapM_ pushL depends
                  tryInvert pid fr mv2ty (block pid (frEqn fr) >> pushL entry)
           _ ->
               do pushR (Right entry)
                  flexRigid depends pid fr

flexFlex :: Monad m => ProbId -> FFEqn -> BMonadFVT m ()
flexFlex = undefined

tryInvert :: Monad m
          => ProbId -> FREqn -> TyFV -> BMonadFVT m () -> BMonadFVT m ()
tryInvert = undefined

simplify :: Monad m
         => ProbId -> ProblemFV -> [ProblemFV] -> BMonadFVT m ()
simplify pid prob probs = go probs []
  where
    go :: Monad m
       => [ProblemFV] -> [ProbId] -> BMonadFVT m ()
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
pendingSolve pid prob []   = do toCtxBwdM (checkProb Solved prob)
                                putProb pid prob Solved
pendingSolve pid prob pids = putProb pid prob (Pending pids)

tryPrune :: Monad m => ProbId -> FREqn -> BMonadFVT m () -> BMonadFVT m ()
tryPrune pid fr@(FREqn _ _ els1 _ t2) m =
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
        return (Just (pis pruned' ty, \v -> lams' unpruned' (v $*$ unpruned)))
  where
    toTriple (fv@(FV (_, nom)), ty') = (nom, fv, ty')
    unpruned' = fmap toTriple unpruned
    pruned'   = fmap toTriple pruned
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
hole = undefined

define :: Monad m
       => [(FreshVar, TyFV)] -> Meta -> TyFV -> TmFV -> BMonadFVT m a
define = undefined
