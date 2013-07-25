module Language.Bertus.Unify where

import Data.Data (Typeable, Data)

import Data.Set (Set)
import qualified Data.Set as Set

import Language.Bertus.Check
import Language.Bertus.Common
import Language.Bertus.Context
import Language.Bertus.Monad
import Language.Bertus.Subst
import Language.Bertus.Tm
import Language.Bertus.Occurs

newtype FreshVar = FV Ref
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
unify pid (Eqn ty1 t1@(Neutr (Meta mv1) els1) ty2 t2@(Neutr (Meta mv2) els2)) =
    tryPrune pid ty2 mv2 els2 ty1 t1 $
    tryPrune pid ty1 mv1 els1 ty2 t2 $
    flexFlex pid ty1 mv1 els1 ty2 mv2 els2
unify pid (Eqn ty1 (Neutr (Meta mv1) els1) ty2 t2) =
    tryPrune pid ty1 mv1 els1 ty1 t2 (flexRigid [] pid ty1 mv1 els1 ty2 t2)
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

flexRigid :: Monad m
          => [EntryFV] -> ProbId
          -> TyFV -> Meta -> [ElimFV] -- lhs
          -> TyFV -> TmFV             -- rhs
          -> BMonadFVT m ()
flexRigid entries pid ty1 mv1 els1 ty2 t2 = undefined

flexFlex :: Monad m
         => ProbId
         -> TyFV -> Meta -> [ElimFV] -- lhs
         -> TyFV -> Meta -> [ElimFV] -- rhs
         -> BMonadFVT m ()
flexFlex pid ty1 mv1 els1 ty2 mv2 els2 = undefined

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

tryPrune :: Monad m
         => ProbId
         -> TyFV -> Meta -> [ElimFV] -- Lhs, ty1 (Neutr (Meta mv1) els1)
         -> TmFV -> TmFV             -- Rhs, ty2 t2
         -> BMonadFVT m () -> BMonadFVT m ()
tryPrune pid ty1 mv1 els1 ty2 t2 m =
    do pars <- gets ctxParams
       pruneds <- prune (boundVs pars `Set.intersection` fvsList els1) t2
       case pruneds of
           pruned : _ -> active pid eqn >> undefined
           []         -> m
  where
    eqn = Eqn ty1 (Neutr (Meta mv1) els1) ty2 t2

boundVs = undefined

prune :: Monad m
      => Set FreshVar -> TmFV -> BMonadFVT m [(FreshVar, TyFV, TmFV -> TmFV)]
prune = undefined

active :: Monad m => ProbId -> EqnFV -> BMonadFVT m ()
active pid eqn = putProb pid (Unify eqn) Active

instantiate :: Monad m => (Meta, TyFV, TmFV -> TmFV) -> BMonadFVT m ()
instantiate pruned@(mv, ty1, f) =
    do entry <- popL
       case entry of
           Entry mv' ty2 Hole | mv == mv' -> undefined
           _                              -> do pushR (Right entry)
                                                instantiate pruned

hole :: Monad m
     => SubsFV -> TyFV -> (TmFV -> BMonadFVT m a) -> BMonadFVT m a
hole subs ty f = undefined
--    do check Type (
