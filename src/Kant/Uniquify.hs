{-# LANGUAGE TupleSections #-}
-- TODO this is *really* ugly, I should really look for some good abstractions
-- and reimplement those functions.
module Kant.Uniquify
    ( Uniquify(..)
    , UniqueM
    , Count
    , revert
    ) where

import           Control.Applicative ((<$>), (<*>), (<$))

import           Control.Monad.State (State, MonadState(..), evalState)
import           Data.Map (Map)
import qualified Data.Map as Map
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

freshBinder :: TBinderT Id -> State Count (TBinderT Id)
freshBinder b = (<$ b) <$> fresh

instance Uniquify TermT where
    uniquify t = packt <$> doUniquify t


doUniquify :: TermV -> UniqueM (TermT Id Id)
doUniquify = uniquify' . collect . separate

instance Uniquify DeclT where
    uniquify (Val n t) = Val n <$> uniquify t
    uniquify (DataD dd) = DataD <$> uniquify dd
    uniquify (Postulate n ty) = Postulate n <$> uniquify ty

packt :: TermT Id Id -> Term
packt (Var (Bound n)) = bound (Text.pack n)
packt (Var (Free n))  = free n
packt (Type l) = Type l
packt (App t₁ t₂) = App (packt t₁) (packt t₂)
packt (Arr b ty₁ ty₂) = Arr (Text.pack <$> b) (packt ty₁) (packt ty₂)
packt (Lam b ty t) = Lam (Text.pack <$> b) (packt ty) (packt t)
packt (Case b t ty brs) =
    Case (Text.pack <$> b) (packt t) (packt ty)
         [(c, map (Text.pack <$>) bs, packt t') | (c, bs, t') <- brs]
packt (Fix b pars ty t) = Fix (Text.pack <$> b) (packPars pars) (packt ty) (packt t)
packt (Constr c tys ts) = Constr c (map packt tys) (map packt ts)

packPars :: [(TBinderT Id, TermT Id Id)] -> [(TBinder, Term)]
packPars pars = [(Text.pack <$> b', packt ty') | (b', ty') <- pars]

uniquify' :: TermT Id Id -> UniqueM (TermT Id Id)
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

uniquifyBrs :: [BranchT Id Id] -> UniqueM [BranchT Id Id]
uniquifyBrs = mapM go
  where
    go (c, bs, t) = do bsFresh <- mapM (\b -> (b,) <$> freshBinder b) bs
                       let t' = foldr (\(b, b') -> substTag b b') t bsFresh
                       return (c, map snd bsFresh, t')

-- uniquifyPars :: [ParamV] -> TermV -> UniqueM ([ParamV], TermV)
uniquifyPars pars ty = paramsFun uniquify' pars ty

-- substTag :: TBinderT Id -> TBinderT Id -> TermT Id Id -> TermT Id Id
substTag Wild        _            t = t
substTag (Bind _ ta) (Bind _ ta') t = subst ta (bound ta') t
substTag _           _            _ = error "Uniquify.substTag': Binder mismatch"

-- substBrsTag :: TBinderT Id -> TBinderT Id -> [BranchV] -> [BranchV]
substBrsTag Wild        _            brs = brs
substBrsTag (Bind _ ta) (Bind _ ta') brs = substBrs ta (bound ta') brs
substBrsTag _           _            _   =
    error "Uniquify.substBrsTag: Binder mismatch"

-- substParsTag :: TBinderT Id -> TBinderT Id -> [ParamT Id Id] -> Term -> ([ParamV], TermV)
substParsTag Wild        _            brs t = (brs, t)
substParsTag (Bind _ ta) (Bind _ ta') brs t = substPars ta (bound ta') brs t
substParsTag _           _            _   _ =
    error "Uniquify.substParsTag: Binder mismatch"

collect :: TermT Void (Either Id Id) -> TermT Id Id
collect (Var (Free v)) = absurd v
collect (Var (Bound (Left n))) = free n
collect (Var (Bound (Right n))) = bound n
collect (Type l) = Type l
collect (App t₁ t₂) = App (collect t₁) (collect t₂)
collect (Arr b ty₁ ty₂) = Arr (collectRight <$> b) (collect ty₁) (collect ty₂)
collect (Lam b ty t) = Lam (collectRight <$> b) (collect ty) (collect t)
collect (Case b t ty brs) =
    Case (collectRight <$> b) (collect t) (collect ty)
         [(c, map (collectRight <$>) bs, collect t') | (c, bs, t') <- brs]
collect (Constr c tys ts) = Constr c (map collect tys) (map collect ts)
collect (Fix b pars ty t) =
    Fix (collectRight <$> b)
        [(collectRight <$> b', collect ty') | (b', ty') <- pars]
        (collect ty) (collect t)

collectRight :: Either Id Id -> Id
collectRight (Right n) = n
collectRight (Left _)  = error "collect: got a Left binder"

separate :: TermV -> TermT Void (Either Id Id)
separate (Var (Free v)) = absurd v
separate (Var (Bound n)) = bound (Left n)
separate (Type l) = Type l
separate (App t₁ t₂) = App (separate t₁) (separate t₂)
separate (Arr b ty₁ ty₂) =
    Arr (Right <$> b) (separate ty₁) (substE' b ty₂)
separate (Lam b ty t) =
    Lam (Right <$> b) (separate ty) (substE' b t)
separate (Case b t ty brs) =
    Case (Right <$> b) (separate t) (substE' b ty) (substBrsE' b brs)
separate (Constr c tys ts) = Constr c (map separate tys) (map separate ts)
separate (Fix b pars ty t) =
    Fix (Right <$> b) pars' ty' (substE' b t)
  where (pars', ty') = paramsFun' separate pars ty

separateBrs :: [BranchV] -> [BranchT Void (Either Id Id)]
separateBrs brs = [ (c, map (Right <$>) bs,
                     foldr (\b t' -> substE b t') (separate t) bs)
                  | (c, bs, t) <- brs]

substE :: TBinderT Id -> TermT Void (Either Id Id)
       -> TermT Void (Either Id Id)
substE (Bind _ ta) t = subst (Left ta) (Var (Bound (Right ta))) t
substE _           t = t

substE' :: TBinderT Id -> TermV -> TermT Void (Either Id Id)
substE' b t = substE b (separate t)

substBrsE :: TBinderT Id -> [BranchT Void (Either Id Id)]
          -> [BranchT Void (Either Id Id)]
substBrsE (Bind _ ta) brs = substBrs (Left ta) (Var (Bound (Right ta))) brs
substBrsE Wild        brs = brs

substBrsE' :: TBinderT Id -> [BranchV] -> [BranchT Void (Either Id Id)]
substBrsE' b brs = substBrsE b (separateBrs brs)

instance Uniquify DataT where
    uniquify (Data c pars₁ l cons) =
        do (pars₁', Type _) <- paramsFun doUniquify pars₁ (Type l)
           let bs = zip (map fst pars₁) (map fst pars₁')
         -- We use this as a placeholder to use the 'paramsFun' functions
               dummy = bound "dummy"
               sub (b, b') ps = fst (substParsTag b b' ps dummy)
           cons' <- sequence [ (\(pars₂', _) -> (c', packPars pars₂')) <$>
                               paramsFun doUniquify (foldr sub pars₂ bs) dummy
                             | (c', pars₂) <- cons]
           return (Data c (packPars pars₁') l cons')


revert :: Term -> TermV
revert t = evalState (revert' t) (ixs, Map.empty)
  where ixs = Map.fromList (zip (Set.toList (collectFree t)) (repeat 0))

collectFree :: Term -> Set Id
collectFree (Var (Free n)) = Set.singleton n
collectFree (Var _) = Set.empty
collectFree (Type _) = Set.empty
collectFree (App t₁ t₂) = collectFree t₁ `Set.union` collectFree t₂
collectFree (Arr _ ty t) = collectFree ty `Set.union` collectFree t
collectFree (Lam _ ty t) = collectFree ty `Set.union` collectFree t
collectFree (Case _ t ty brs) =
    collectFree t `Set.union` collectFree ty `Set.union`
    Set.unions [collectFree t' | (_, _, t') <- brs]
collectFree (Constr _ tys ts) =
    Set.unions (map collectFree tys) `Set.union` Set.unions (map collectFree ts)
collectFree (Fix _ pars ty t) =
    Set.unions [collectFree t' | (_, t') <- pars] `Set.union`
    collectFree ty `Set.union` collectFree t

type RevertM = State (Map Id Int, Map Tag Id)

getName :: Tag -> RevertM Id
getName ta = do (ixs, vs) <- get
                let n  = vs Map.! ta
                    ix = ixs Map.! n
                return (n ++ (if ix > 0 then show ix else ""))

bumpName :: TBinder -> RevertM (TBinderT Id)
bumpName Wild        = return Wild
bumpName (Bind n ta) = do (ixs, vs) <- get
                          let ix = maybe 0 (+1) (Map.lookup n ixs)
                          put (Map.insert n ix ixs, Map.insert ta n vs)
                          Bind n <$> getName ta

revert' :: Term -> RevertM TermV
-- TODO don't worry about duplicate names in different branches
revert' (Var (Free n)) = return (bound n)
revert' (Var (Bound ta)) = bound <$> getName ta
revert' (Type l) = return (Type l)
revert' (Arr b ty₁ ty₂) =
    Arr <$> bumpName b <*> revert' ty₁ <*> revert' ty₂
revert' (App t₁ t₂) = App <$> revert' t₁ <*> revert' t₂
revert' (Lam b ty t) = Lam <$> bumpName b <*> revert' ty <*> revert' t
revert' (Case b t ty brs) =
    Case <$> bumpName b <*> revert' t <*> revert' ty
         <*> sequence [ do bs' <- mapM bumpName bs
                           (c, bs',) <$> revert' t'
                      | (c, bs, t') <- brs ]
revert' (Fix b pars ty t) =
    do b' <- bumpName b
       (pars', ty') <- paramsFun revert' pars ty
       Fix b' pars' ty' <$> revert' t
revert' (Constr c tys ts) = Constr c <$> mapM revert' tys <*> mapM revert' ts

