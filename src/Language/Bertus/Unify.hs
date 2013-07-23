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
    twinsEqn = Eqn (inst (fmap F cod1) xL) (fmap F t1 $$ xL)
                   (inst (fmap F cod2) xR) (fmap F t2 $$ xR)
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

simplify :: forall v m. (Eq v, Monad m)
         => ProbId -> Problem v -> [Problem v] -> BMonadT v m ()
simplify pid prob probs = go probs []
  where
    go :: (Eq v, Monad m)
       => [Problem v] -> [ProbId] -> BMonadT v m ()
    go []               pids = pendingSolve pid prob pids
    go (prob' : probs') pids = subgoal prob' (go probs' . (: pids))

    -- TODO check that the `wrapProb' is indeed not needed
    subgoal :: Monad m
            => Problem v -> (ProbId -> BMonadT v m a) -> BMonadT v m a
    subgoal prob' f =
        do pid' <- probId <$> fresh
           pushL (Prob pid' prob' Active)
           x <- f pid'
           goL
           return x

-- TODO check that the `wrapProb' is not needed
putProb :: Monad m => ProbId -> Problem v -> ProblemState -> BMonadT v m ()
putProb pid prob pst = pushR (Right (Prob pid prob pst))

pendingSolve :: (Eq v, Monad m)
             => ProbId -> Problem v -> [ProbId] -> BMonadT v m ()
pendingSolve pid prob []   = do checkProb Solved prob
                                putProb pid prob Solved
pendingSolve pid prob pids = putProb pid prob (Pending pids)

tryPrune :: ProbId -> Eqn v -> BMonadT v m () -> BMonadT v m ()
tryPrune = undefined

flexFlex :: (Monad m, Eq v) => ProbId -> Eqn v -> BMonadT v m ()
flexFlex = undefined

flexRigid :: (Monad m, Eq v) => [Entry v] -> ProbId -> Eqn v -> BMonadT v m ()
flexRigid = undefined

rigidRigid :: (Monad m, Eq v) => Eqn v -> BMonadT v m [Eqn v]
rigidRigid = undefined
