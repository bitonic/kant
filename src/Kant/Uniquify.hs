module Kant.Uniquify
    ( Uniquify(..)
    , UniqueM
    , Count
    , revert
    ) where

import           Control.Applicative ((<$>), (<*>), (<$))
import           Control.Arrow (second)

import           Control.Monad.State (State, MonadState(..))
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text

import           Data.Void

import           Kant.Term
import           Kant.Name

type Count = Integer

type UniqueM = State Count

class Uniquify f where
    uniquify :: f Void Id -> UniqueM (f Id Tag)

fresh :: State Count Id
fresh = do ta <- get
           put (ta + 1)
           return (show ta)

freshBinder :: Binder Id -> State Count (Binder Id)
freshBinder b = (<$ b) <$> fresh

instance Uniquify TermT where
    uniquify t = do t' <- uniquify' t
                    let (vs, vsBound) = collect t'
                    return (replace (Set.difference vs vsBound) t')

substTag :: Binder Id -> Binder Id -> TermV -> TermV
substTag Wild      _          t = t
substTag (Bind ta) (Bind ta') t = subst ta (\n -> Var (Bound n ta')) t
substTag _         _          _ = error "Uniquify.substTag': Binder mismatch"

substBrsTag :: Binder Id -> Binder Id -> [BranchV] -> [BranchV]
substBrsTag Wild      _          brs = brs
substBrsTag (Bind ta) (Bind ta') brs = substBrs ta (\n -> Var (Bound n ta')) brs
substBrsTag _         _          _   =
    error "Uniquify.substBrsTag: Binder mismatch"

substParsTag :: Binder Id -> Binder Id -> [ParamV] -> TermV -> ([ParamV], TermV)
substParsTag Wild       _         brs t = (brs, t)
substParsTag (Bind ta) (Bind ta') brs t = substPars ta (\n -> Var (Bound n ta')) brs t
substParsTag _         _          _   _ =
    error "Uniquify.substParsTag: Binder mismatch"

uniquify' :: TermV -> UniqueM TermV
uniquify' t@(Var _) = return t
uniquify' t@(Type _) = return t
uniquify' (App t₁ t₂) = App <$> uniquify' t₁ <*> uniquify' t₂
uniquify' (Arr b ty₁ ty₂) =
    do b' <- freshBinder b
       Arr b' <$> uniquify' ty₁ <*> uniquify' (substTag b b' ty₂)
uniquify' (Lam b ty t) =
    do b' <- freshBinder b
       Lam b' <$> uniquify' ty <*> uniquify' (substTag b b' t)
uniquify' (Case b t ty brs) =
    do b' <- freshBinder b
       Case b' <$> uniquify' t <*> uniquify' (substTag b b' ty)
               <*> uniquifyBrs (substBrsTag b b' brs)
uniquify' (Fix b pars ty t) =
    do b' <- freshBinder b
       (pars', ty') <- uncurry uniquifyPars (substParsTag b b' pars ty)
       Fix b' pars' ty' <$> uniquify' (substTag b b' t)
uniquify' (Constr c tys ts) = Constr c <$> mapM uniquify' tys <*> mapM uniquify' ts

uniquifyBrs :: [BranchV] -> UniqueM [BranchV]
uniquifyBrs = mapM go
  where
    go :: BranchV -> UniqueM BranchV
    go (c, bs, t) = do bsFresh <- mapM (\b -> (,) b <$> freshBinder b) bs
                       let t' = foldr (\(b, b') -> substTag b b') t bsFresh
                       return (c, map snd bsFresh, t')

uniquifyPars :: [ParamV] -> TermV -> UniqueM ([ParamV], TermV)
uniquifyPars pars ty = paramsFun uniquify' pars ty

collect :: TermV -> (Set Id, Set Id)
collect (Var (Free v)) = absurd v
collect (Var (Bound _ ta)) = lsingle ta
collect (Type _) = (Set.empty, Set.empty)
collect (App t₁ t₂) = collect t₁ `dunion` collect t₂
collect (Arr b ty₁ ty₂) = rsingle b `dunion` collect ty₁ `dunion` collect ty₂
collect (Lam b ty t) = rsingle b `dunion` collect ty `dunion` collect t
collect (Case b t ty brs) =
    rsingle b `dunion` collect t `dunion` collect ty `dunion`
    dunions [dunions (map rsingle bs) `dunion` collect t' | (_, bs, t') <- brs]
collect (Constr _ tys ts) = dunions (map collect tys) `dunion` dunions (map collect ts)
collect (Fix b pars ty t) =
    rsingle b `dunion` collectPars pars `dunion` collect ty `dunion` collect t

collectPars :: [(Binder Id, TermV)] -> (Set Id, Set Id)
collectPars pars = dunions [rsingle b' `dunion` collect ty' | (b', ty') <- pars]

lsingle :: a -> (Set a, Set b)
lsingle ta = (Set.singleton ta, Set.empty)

rsingle :: Binder t -> (Set a, Set t)
rsingle Wild = (Set.empty, Set.empty)
rsingle (Bind ta) = (Set.empty, Set.singleton ta)

dunion :: (Set Id, Set Id) -> (Set Id, Set Id) -> (Set Id, Set Id)
(vs, vsb) `dunion` (vs', vsb') = (Set.union vs vs', Set.union vsb vsb')

dunions :: [(Set Id, Set Id)] -> (Set Id, Set Id)
dunions []  = (Set.empty, Set.empty)
dunions vss = foldr1 dunion vss

replace :: Set Id -> TermV -> Term
replace _  (Var (Free v)) = absurd v
replace vs (Var (Bound n v)) | Set.member v vs = Var (Free n)
replace _  (Var (Bound n v)) = Var (Bound n (Text.pack v))
replace _  (Type l) = Type l
replace vs (App t₁ t₂) = App (replace vs t₁) (replace vs t₂)
replace vs (Arr b ty₁ ty₂) = Arr (Text.pack <$> b) (replace vs ty₁) (replace vs ty₂)
replace vs (Lam b ty t) = Lam (Text.pack <$> b) (replace vs ty) (replace vs t)
replace vs (Case b t ty brs) =
    Case (Text.pack <$> b) (replace vs t) (replace vs ty)
         [(c, map (Text.pack <$>) bs, replace vs t') | (c, bs, t') <- brs]
replace vs (Constr c tys ts) = Constr c (map (replace vs) tys) (map (replace vs) ts)
replace vs (Fix b pars ty t) = Fix (Text.pack <$> b) (replacePars vs pars)
                                   (replace vs ty) (replace vs t)

replacePars :: Set Id -> [ParamV] -> [Param]
replacePars vs pars = [(Text.pack <$> b', replace vs ty') | (b', ty') <- pars]

instance Uniquify DataT where
    uniquify (Data c pars₁ l cons) =
        do (pars₁', Type _) <- paramsFun uniquify' pars₁ (Type l)
           let bs = zip (map fst pars₁) (map fst pars₁')
               -- We use this as a placeholder to use the 'paramsFun' functions
               dummy = Var (bound "dummy")
               sub (b, b') ps = fst (substParsTag b b' ps dummy)
           cons' <- sequence
                    [ ((,) c' . fst) <$> uniquifyPars (foldr sub pars₂ bs) dummy
                    | (c', pars₂) <- cons]
           let dd = Data c pars₁' l cons'
               (vs, vsBound) = collectData dd
           return (replaceData (Set.difference vs vsBound) dd)

collectData :: DataV -> (Set Id, Set Id)
collectData (Data _ pars _ cons) =
    collectPars pars `dunion` dunions (map (collectPars . snd) cons)

replaceData :: Set Id -> DataV -> Data
replaceData vs (Data c pars l cons) =
    Data c (replacePars vs pars) l (map (second (replacePars vs)) cons)

instance Uniquify DeclT where
    uniquify (Val n t) = Val n <$> uniquify t
    uniquify (DataD dd) = DataD <$> uniquify dd
    uniquify (Postulate n ty) = Postulate n <$> uniquify ty

revert :: Term -> TermV
revert (Var (Free n)) = Var (bound n)
-- TODO make names better
revert (Var (Bound _ v)) = Var (bound (Text.unpack v))
revert (Type l) = Type l
revert (App t₁ t₂) = App (revert t₁) (revert t₂)
revert (Arr b ty₁ ty₂) = Arr (Text.unpack <$> b) (revert ty₁) (revert ty₂)
revert (Lam b ty t) = Lam (Text.unpack <$> b) (revert ty) (revert t)
revert (Case b t ty brs) =
    Case (Text.unpack <$> b) (revert t) (revert ty)
         [(c, map (Text.unpack <$>) bs, revert t') | (c, bs, t') <- brs]
revert (Constr c tys ts) = Constr c (map revert tys) (map revert ts)
revert (Fix b pars ty t) = Fix (Text.unpack <$> b)
                          [(Text.unpack <$> b', revert ty') | (b', ty') <- pars]
                          (revert ty) (revert t)
