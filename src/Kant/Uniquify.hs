module Kant.Uniquify
    ( Uniquify(..)
    , UniqueM
    , Count
    ) where

import           Control.Applicative ((<$>), (<*>), (<$))

import           Control.Monad.State (State, MonadState(..))
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text

import           Data.Void

import           Kant.Term

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
       Fix b pars' ty' <$> uniquify' (substTag b b' t)
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
collect = undefined

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
replace vs (Fix b pars ty t) = Fix (Text.pack <$> b)
                                   [ (Text.pack <$> b', replace vs ty')
                                   | (b', ty') <- pars] (replace vs ty) (replace vs t)

instance Uniquify DataT
