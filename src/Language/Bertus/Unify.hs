module Language.Bertus.Unify where

import Language.Bertus.Check
import Language.Bertus.Common
import Language.Bertus.Context
import Language.Bertus.Monad
import Language.Bertus.Subst
import Language.Bertus.Tm

unify :: (Eq v, Monad m) => ProbId -> Eqn v -> BMonadT v m ()
unify pid eqn@(Eqn (Bind Pi dom1 cod1) t1 (Bind Pi dom2 cod2) t2) =
    simplify pid (Unify eqn)
             [ Unify (Eqn Type dom1 Type dom2)
             , All (Twins dom1 dom2) (Unify twinsEqn) ]
  where
    (xL, xR) = (var (B "x") TwinL, var (B "x") TwinR)
    twinsEqn = Eqn (inst (nest cod1) xL) (nest t1 $$ xL)
                   (inst (nest cod2) xR) (nest t2 $$ xR)
unify pid eqn@(Eqn (Bind Sig fsty1 snty1) t1 (Bind Sig fsty2 snty2) t2) =
    simplify pid (Unify eqn)
             [ Unify (Eqn fsty1 fs1 fsty2 fs2)
             , Unify (Eqn (inst snty1 fs1) sn1 (inst snty2 fs2) sn2) ]
  where
    (fs1, sn1) = (t1 %% Fst, t1 %% Snd)
    (fs2, sn2) = (t2 %% Fst, t2 %% Snd)
unify pid eqn@(Eqn _ (Neutr (Meta _) _) _ (Neutr (Meta _) _)) =
    tryPrune pid eqn (tryPrune pid (sym eqn) (flexFlex pid eqn))
unify pid eqn@(Eqn _ (Neutr (Meta _) _) _ _) =
    tryPrune pid eqn (flexRigid [] pid eqn)
unify pid eqn@(Eqn _ _ _ (Neutr (Meta _) _)) =
    unify pid (sym eqn)
unify pid eqn =
    rigidRigid eqn >>= simplify pid (Unify eqn) . map Unify

rigidRigid :: (Monad m, Eq v) => Eqn v -> BMonadT v m [Eqn v]
rigidRigid (Eqn Type Type Type Type) = return []
rigidRigid (Eqn Type (Bind bi1 dom1 cod1) Type (Bind bi2 dom2 cod2))
    | bi1 == bi2 =
    return [ Eqn Type dom1 Type dom2
           , Eqn (dom1 --> Type) (Lam cod1) (dom2 --> Type) (Lam cod2) ]
-- TODO throwing away types
rigidRigid (Eqn _ (Neutr (Var v1 tw1) els1) _ (Neutr (Var v2 tw2) els2))
    | v1 == v2 =
    do tyv1 <- lookupVar v1 tw1
       tyv2 <- lookupVar v2 tw2
       (Eqn Type tyv1 Type tyv2 :) <$>
           matchSpine tyv1 (var v1 tw1) els1 tyv2 (var v2 tw2) els2
rigidRigid _ =
    throwError "rigidRigid mismatch"

matchSpine :: (Monad m, Eq v)
           => Ty v -> Tm v -> [Elim v] -> Ty v -> Tm v -> [Elim v]
           -> BMonadT v m [Eqn v]
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
matchSpine (Bind Sig _ snty1) t1 (Fst : els1)
           (Bind Sig _ snty2) t2 (Fst : els2) =
    matchSpine (snty1 `inst` fs1) sn1 els1 (snty2 `inst` fs2) sn2 els2
  where
    (fs1, sn1) = (t1 %% Fst, t1 %% Snd)
    (fs2, sn2) = (t2 %% Fst, t2 %% Snd)
matchSpine _ _ _ _ _ _ = throwError "spine mismatch"

simplify :: forall v m. (Eq v, Monad m)
         => ProbId -> Problem v -> [Problem v] -> BMonadT v m ()
simplify pid prob probs = go probs []
  where
    -- TODO check that the `wrapProb' is not needed
    go :: (Eq v, Monad m)
       => [Problem v] -> [ProbId] -> BMonadT v m ()
    go []               pids = pendingSolve pid prob pids
    go (prob' : probs') pids = do pid' <- probId <$> fresh
                                  pushL (Prob pid' prob' Active)
                                  go probs' (pid' : pids) <* goL

-- TODO check that the `wrapProb' is not needed
putProb :: Monad m => ProbId -> Problem v -> ProblemState -> BMonadT v m ()
putProb pid prob pst = pushR (Right (Prob pid prob pst))

pendingSolve :: (Eq v, Monad m)
             => ProbId -> Problem v -> [ProbId] -> BMonadT v m ()
pendingSolve pid prob []   = checkProb Solved prob *> putProb pid prob Solved
pendingSolve pid prob pids = putProb pid prob (Pending pids)

tryPrune :: ProbId -> Eqn v -> BMonadT v m () -> BMonadT v m ()
tryPrune = undefined

flexFlex :: (Monad m, Eq v) => ProbId -> Eqn v -> BMonadT v m ()
flexFlex = undefined

flexRigid :: (Monad m, Eq v) => [Entry v] -> ProbId -> Eqn v -> BMonadT v m ()
flexRigid = undefined
