{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Kant.Sugar
     ( Id
     , ConId
     , Level
     , SModule(..)
     , SDecl(..)
     , SValParams(..)
     , SParam
     , SConstr
     , STerm(..)
     , scase
     , SBranch
     , Desugar(..)
     , Distill(..)
     ) where

import           Control.Applicative ((<$))
import           Control.Arrow (second, (+++))
import           Data.Foldable (Foldable)
import           Data.List (groupBy)
import           Data.Maybe (fromMaybe, isJust)
import           Prelude hiding ((!!), length, splitAt, drop)
import qualified Prelude

import qualified Data.Set as Set

import           Bound
import           Bound.Name
import           Bound.Scope
import           Numeric.Natural

import           Kant.Common
import           Kant.Term

newtype SModule = SModule {unSModule :: [SDecl]}

data SDecl
    = SVal Id SValParams STerm STerm
    | SPostulate Id STerm
    | SData ConId [SParam] Level [SConstr]
    deriving (Show)

data SValParams = SValParams [SParam] (Maybe [SParam])
    deriving (Show)
type SParam = (Maybe [Id], STerm)
type SConstr = (ConId, [SParam])

-- TODO add let bindings
-- | A term matching what we parse, which can be 'desugar'ed and 'distill'ed
--   into a 'Term'.
data STerm
    = SVar Id
    | SType Level
    | SLam [SParam] STerm
    | SApp STerm STerm
    | SArr [SParam] STerm
      -- TODO add a way to match on non-variables
      -- | Pattern matching.  Note that here we demand a variable as scrutined
      --   so that the return type can refer to that directly.
    | SCase Id STerm [SBranch]
    | SFix (Maybe Id) [SParam] STerm STerm
    deriving (Show)

-- | Checks that all variables matched in branches are distinct.  Returns
--   @'Left' v@ if `v' is duplicate somewhere.
scase :: Id -> STerm -> [SBranch] -> Either Id STerm
scase n₁ ty brs =
    SCase n₁ ty brs
    <$ mapM (foldr (\n₂ se -> se >>= \s ->
                     if Set.member n₂ s then Left n₂
                     else Right (Set.insert n₂ s))
                   (Right Set.empty))
            [ns | (_, ns, _) <- brs]

type SBranch = ( ConId          -- Constructor
               , [Id]           -- Matched variables
               , STerm
               )

-- TODO add errors to desugar:
-- * the 'error' below
-- * the assume distillFix below
-- ...
class Desugar a b where
    desugar :: a -> b

instance a ~ Module => Desugar SModule a where
    desugar (SModule decls) = Module (map desugar decls)

instance a ~ Decl => Desugar SDecl a where
    -- TODO make the fix machinery more flexible, we want to be able to fix only
    -- certain arguments.
    desugar (SVal n pars ty t) =
        Val n (desugar (buildVal n pars ty t))
    desugar (SPostulate n ty) = Postulate n (desugar ty)
    desugar (SData c pars l cons) =
        DataD (Data c (desugarPars pars) l (map (second desugarPars) cons))

-- TODO broken, fix soon, the rec call should include the lambdas
buildVal :: Id -> SValParams -> STerm -> STerm -> STerm
buildVal n (SValParams pars mfpars) ty t =
    SLam pars $
    case mfpars of
        Just fpars -> SFix (Just n) fpars ty (removeNotFix n (length pars) t)
        Nothing    -> t

removeNotFix :: Id -> Natural -> STerm -> STerm
removeNotFix _ _ t@(SVar _) = t
removeNotFix _ _ t@(SType _) = t
removeNotFix n i (SLam pars t) =
    case rnfPars n i pars of
        Left pars'  -> SLam pars' (removeNotFix n i t)
        Right pars' -> SLam pars' t
removeNotFix n₁ i (SApp (SVar n₂) t) =
     -- TODO emit an error if the application has less than `i' things
     if n₁ == n₂ then foldl SApp (SVar n₂) (drop i (go t))
     else SApp (SVar n₂) (removeNotFix n₁ i t)
  where go (SApp t₁ t₂) = go t₁ ++ [t₂]
        go t₁           = [t₁]
removeNotFix n i (SApp t₁ t₂) = SApp (removeNotFix n i t₁) (removeNotFix n i t₂)
removeNotFix n i (SArr pars t) =
    case rnfPars n i pars of
        Left pars'  -> SArr pars' (removeNotFix n i t)
        Right pars' -> SArr pars' t
removeNotFix n₁ i (SCase n₂ ty brs) =
    SCase n₂ (removeNotFix n₁ i ty) (rnfBrs n₁ i brs)
removeNotFix n₁ _ t@(SFix (Just n₂) _ _ _) | n₁ == n₂ = t
removeNotFix n i (SFix nm pars ty t) =
    case rnfPars n i pars of
        Left pars'  -> SFix nm pars' (removeNotFix n i ty) (removeNotFix n i t)
        Right pars' -> SFix nm pars' ty t

leftRight :: (a -> b) -> Either a a -> Either b b
leftRight f = f +++ f

rnfPars :: Id -> Natural -> [SParam] -> Either [SParam] [SParam]
rnfPars _ _ [] = Left []
rnfPars n i ((Nothing, ty) : pars) = leftRight (par :) (rnfPars n i pars)
  where par = (Nothing, removeNotFix n i ty)
rnfPars n i ((Just [], _) : pars) = rnfPars n i pars
rnfPars n i ((Just ns, ty) : pars) =
    case elemIndex n ns of
        Nothing -> leftRight ((Just ns, removeNotFix n i ty) :) (rnfPars n i pars)
        Just 0  -> Right ((Just ns, ty) : pars)
        Just j  -> let (ns', ns'') = splitAt (j+1) ns
                   in Right ((Just ns', removeNotFix n i ty) : (Just ns'', ty) : pars)

rnfBrs :: Id -> Natural -> [SBranch] -> [SBranch]
rnfBrs n i brs = [ (c, ns, if n `elem` ns then t else removeNotFix n i t)
                 | (c, ns, t) <- brs ]

desugarPars :: [SParam] -> [Param]
desugarPars pars =
    concat [zip (fromMaybe [discarded] mns) (repeat (desugar t)) | (mns, t) <- pars]

instance a ~ (TermT Id) => Desugar STerm a where
    desugar (SVar n)            = Var n
    desugar (SType l)           = Type l
    desugar (SLam pars t)       = lams (desugarPars pars) (desugar t)
    desugar (SApp t₁ t₂)        = App (desugar t₁) (desugar t₂)
    desugar (SArr pars ty)      = desugarArr pars ty
    desugar (SCase n ty brs)    =
        case_ (Var n) n (desugar ty) [(c, ns, desugar t) | (c, ns, t) <- brs]
    desugar (SFix nm pars ty t) =
        fix (discardedM nm) (desugarPars pars) (desugar ty) (desugar t)

desugarArr :: [SParam] -> STerm -> Term
desugarArr []                          ty  = desugar ty
desugarArr ((Nothing,     ty₁) : pars) ty₂ = arr (desugar ty₁) (desugarArr pars ty₂)
desugarArr ((Just (n:ns), ty₁) : pars) ty₂ =
    pi_ n (desugar ty₁) (desugarArr ((Just ns, ty₁) : pars) ty₂)
desugarArr ((Just [],     _)   : pars) ty  = desugarArr pars ty

class Distill a b where
    distill :: a -> b

instance (a ~ STerm, b ~ Id) => Distill (TermT b) a where
    -- TODO make names unique
    distill (Var n) = SVar n
    distill (Type l) = SType l
    distill (Arr ty s) =
        SArr [(par, distill ty)] (distill (instantiate1 (Var n) s))
      -- TODO group equal types
      where (par, n) = case scopeVar s of
                           Nothing -> (Nothing, discarded)
                           Just n' -> (Just [n'], n')
    distill (App t₁ t₂) = SApp (distill t₁) (distill t₂)
    distill to@(Lam _ _)  =
        let (pars, t) = go to in SLam (distillPars pars) (distill t)
      where
         go (Lam ty s) = let (n, t)     = freshScope s
                             (pars, t') = go t
                         in ((n, ty) : pars, t')
         go t          = ([], t)
    distill (Case v@(Var n) (CaseT s brs)) =
        SCase n (distill (instantiate1 v s))
              [ let (ns, s') = freshScopeNat ss i
                in (c, ns, distill (instantiate1 v s'))
              | BranchT c i ss <- brs ]
    distill (Case _ _) = error "distill: panic, got a non-var scrutined"
    distill (Constr c tys ts) =
        foldl1 SApp (SVar c : map distill tys ++ map distill ts)
    distill (Fix ty tf) =
        SFix nm pars ty' t where (nm, pars, ty', t) = distillFix ty tf

distillPars :: [Param] -> [SParam]
distillPars pars =
    [(sequence (map fst pars'), distill ty) | pars'@((_, ty):_) <- go]
  where
    go = groupBy (\(mn₁, ty₁) (mn₂, ty₂) -> isJust mn₁ && isJust mn₂ && ty₁ == ty₂)
         [(if n == discarded then Nothing else Just n, t) | (n, t) <- pars]

distillFix :: Term -> FixT TermT Id  -> (Maybe Id, [SParam], STerm, STerm)
distillFix ty (FixT i ss) =
    -- TODO we assume that the arr is well formed
    let Just (pars, ty') = unrollArr i ty
        (pars', rest)    = splitAt i pars
        nm               = scopeVar (fromScope ss)
        ns               = [(j, n') | Name n' j <- bindings ss]
        pars''           = mergeBi pars' ns
    in (nm, distillPars pars'', distill (pis rest ty'),
        distill (instantiateNatU (map (Var . fst) pars'') (Var (discardedM nm)) ss))
  where
    mergeBi pars ns =
        [ (if n' == discarded then discardedM (lookup j ns) else n', ty')
        | (j, (n', ty')) <- zip [0..] pars ]

freshScope :: TScope Id -> (Id, Term)
freshScope s = (n, instantiate1 (Var n) s)
  where n = discardedM (scopeVar s)

-- INVARIANT Again, we assume that the bound 'Natural's are all below the
-- provided 'Natural'.
freshScopeNat :: (Monad f, Foldable f)
              => Scope (TName Natural) f Id -> Natural -> ([Id], f Id)
freshScopeNat s i = (vars', instantiateList (map return vars') s)
  where vars = [ (ix, n) | Name n ix <- bindings s ]
        vars' = [ discardedM (lookup ix vars)
                | ix <- if i > 0 then [0..(i-1)] else [] ]
