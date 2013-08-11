module Language.Bertus.Check where

import Language.Bertus.Common
import Language.Bertus.Context
import Language.Bertus.Monad
import Language.Bertus.Subst
import Language.Bertus.Tm

typecheck :: (Eq v, Monad m) => Ty v -> Tm v -> BMonadBwdT v m Bool
typecheck ty t =
    (True <$ check ty t) `catchError` const (return False)

check :: (Eq v, Monad m) => Ty v -> Tm v -> BMonadBwdT v m ()
check Type Type =
    return ()
check (Bind Pi dom cod) (Lam t) =
    nestBwd (Param dom) (check cod t)
check (Bind Sig fsty snty) (Pair fs sn) =
    do check fsty fs
       check (inst snty fs) sn
check ty (Neutr he els) =
    do hety <- infer he
       ty' <- checkSpine hety (Neutr he []) els
       eq <- ty <-> ty'
       unless eq (throwError "mismatching types")
check _ _ =
    throwError "canonical inhabitant of non-canonical type"

checkSpine :: (Eq v, Monad m)
           => Ty v -> Tm v -> [Elim v] -> BMonadBwdT v m (Ty v)
checkSpine ty _ [] =
    return ty
checkSpine (Bind Pi dom cod) t (App u : els) =
    do check dom u
       checkSpine (inst cod u) (t $$ u) els
checkSpine (Bind Sig fsty _) t (Fst : els) =
    do checkSpine fsty (t %% Fst) els
checkSpine (Bind Sig _ snty) t (Snd : els) =
    checkSpine (inst snty (t %% Fst)) (t %% Snd) els
checkSpine _ _ _ = throwError "checkSpine error"

infer :: Monad m => Head v -> BMonadBwdT v m (Ty v)
infer (Var v tw) = lookupVar lookupCtxBwd v tw
infer (Meta mv)  = lookupMeta mv

quote :: Monad m => Ty v -> Tm v -> BMonadBwdT v m (Tm v)
quote (Bind Pi dom cod) t =
    Lam <$> nestBwd (Param dom) (quote cod (nest t $$ var' dummy))
quote (Bind Sig fsty snty) t =
    Pair <$> quote fsty fs <*> quote (inst snty fs) (t %% Snd)
  where fs = t %% Fst
quote Type Type =
    return Type
quote Type (Bind bi lhs rhs) =
    Bind bi <$> quote Type lhs <*> nestBwd (Param lhs) (quote Type rhs)
-- TODO throwing away the type
quote _ (Neutr he els) =
    do ty <- infer he
       quoteSpine ty (head_ he) els
quote _ _ =
    error "quote"

quoteSpine :: Monad m => Ty v -> Tm v -> [Elim v] -> BMonadBwdT v m (Tm v)
quoteSpine _ t [] =
    return t
quoteSpine (Bind Pi dom cod) t (App u : els) =
    do u' <- quote dom u
       quoteSpine (inst cod u') (t $$ u') els
quoteSpine (Bind Sig fsty _) t (Fst : els) =
    quoteSpine fsty (t %% Fst) els
quoteSpine (Bind Sig _ snty) t (Snd : els) =
    quoteSpine (inst snty (t %% Fst)) (t %% Snd) els
quoteSpine _ _ _ =
    error "quoteSpine"

equal :: (Eq v, Monad m) => Ty v -> Tm v -> Tm v -> BMonadBwdT v m Bool
equal ty t1 t2 = (==) <$> quote ty t1 <*> quote ty t2

(<->) :: (Eq v, Monad m) => Ty v -> Ty v -> BMonadBwdT v m Bool
ty1 <-> ty2 = equal Type ty1 ty2

isReflexive :: (Eq v, Monad m) => Eqn v -> BMonadBwdT v m Bool
isReflexive (Eqn ty1 t1 ty2 t2) =
    do eq <- ty1 <-> ty2
       if eq then equal ty1 t1 t2 else return False

checkProb :: (Eq v, Monad m)
          => ProblemState -> Problem v -> BMonadBwdT v m ()
checkProb pst (Unify (Eqn ty1 t1 ty2 t2)) =
    do check Type ty1
       check ty1  t1
       check Type ty2
       check t2   t2
       if pst == Solved
           then do eq <- isReflexive (Eqn ty1 t1 ty2 t2)
                   unless eq (error "checkProb: not unified")
           else undefined
checkProb pst (All (Param ty) prob) =
    do check Type ty
       nestBwd (Param ty) (checkProb pst prob)
checkProb pst (All (Twins ty1 ty2) prob) =
    do check Type ty1
       check Type ty2
       nestBwd (Twins ty1 ty2) (checkProb pst prob)
