{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.Sugar
     ( -- * Abstract syntax tree
       SModule(..)
     , SDecl(..)
     , SValParams(..)
     , SParam
     , SConstr
     , STerm(..)
     , scase
     , SBranch
       -- * Desugaring
     , desugar
       -- * Distilling
     , distill
     ) where

import           Control.Applicative ((<$))
import           Control.Arrow (second, (+++))
import           Data.Foldable (Foldable)
import           Data.List (groupBy, elemIndex)
import           Data.Maybe (fromMaybe, isJust)

import qualified Data.Set as Set

import           Data.Void
import           Numeric.Natural

import           Kant.Name
import           Kant.Binder
import           Kant.Term

newtype SModule = SModule {unSModule :: [SDecl]}

data SDecl
    = SVal Id SValParams STerm STerm
    | SPostulate Id STerm
    | SData ConId [SParam] Level [SConstr]
    deriving (Show)

data SValParams = SValParams [SParam] (Maybe [SParam])
    deriving (Show)
type SParam = (Binder [Id], STerm)
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
    | SFix (Binder Id) [SParam] STerm STerm
    deriving (Show)

-- | Checks that all variables matched in branches are distinct.  Returns
--   @'Left' v@ if `v' is duplicate somewhere.
scase :: Id -> STerm -> [SBranch] -> Either Id STerm
scase n₁ ty brs =
    SCase n₁ ty brs
    <$ mapM (foldr (\b se -> se >>= \s ->
                     case b of
                         Wild    -> Right s
                         Name n₂ | Set.member n₂ s -> Left n₂
                         Name n₂ -> Right (Set.insert n₂ s))
                   (Right Set.empty))
            [ns | (_, ns, _) <- brs]

type SBranch = ( ConId          -- Constructor
               , [Binder Id]    -- Matched variables
               , STerm
               )

-- TODO add errors to desugar:
-- * the 'error' below
-- * the assume distillFix below
-- ...
class Desugar a b where
    desugar :: a -> b

instance a ~ ModuleV  => Desugar SModule a where
    desugar (SModule decls) = Module (map desugar decls)

instance a ~ DeclV => Desugar SDecl a where
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
        Just fpars -> SFix (Name n) fpars ty (removeNotFix n (length pars) t)
        Nothing    -> t

unrollSArr :: STerm -> [STerm]
unrollSArr (SApp t₁ t₂) = unrollSArr t₁ ++ [t₂]
unrollSArr t₁           = [t₁]

removeNotFix :: Id -> Int -> STerm -> STerm
removeNotFix _ _ t@(SVar _) = t
removeNotFix _ _ t@(SType _) = t
removeNotFix n i (SLam pars t) =
    case rnfPars n i pars of
        Left pars'  -> SLam pars' (removeNotFix n i t)
        Right pars' -> SLam pars' t
removeNotFix n₁ i (unrollSArr -> (SVar n₂ : ts)) | n₁ == n₂ =
    -- TODO emit an error if the application has less than `i' things
    foldl SApp (SVar n₂) (drop i (map (removeNotFix n₁ i) ts))
removeNotFix n i (SApp t₁ t₂) = SApp (removeNotFix n i t₁) (removeNotFix n i t₂)
removeNotFix n i (SArr pars t) =
    case rnfPars n i pars of
        Left pars'  -> SArr pars' (removeNotFix n i t)
        Right pars' -> SArr pars' t
removeNotFix n₁ i (SCase n₂ ty brs) =
    SCase n₂ (removeNotFix n₁ i ty) (rnfBrs n₁ i brs)
removeNotFix n₁ _ t@(SFix (Name n₂) _ _ _) | n₁ == n₂ = t
removeNotFix n i (SFix nm pars ty t) =
    case rnfPars n i pars of
        Left pars'  -> SFix nm pars' (removeNotFix n i ty) (removeNotFix n i t)
        Right pars' -> SFix nm pars' ty t

leftRight :: (a -> b) -> Either a a -> Either b b
leftRight f = f +++ f

rnfPars :: Id -> Int -> [SParam] -> Either [SParam] [SParam]
rnfPars _ _ [] = Left []
rnfPars n i ((Wild, ty) : pars) = leftRight (par :) (rnfPars n i pars)
  where par = (Wild, removeNotFix n i ty)
rnfPars n i ((Name [], _) : pars) = rnfPars n i pars
rnfPars n i ((Name ns, ty) : pars) =
    case elemIndex n ns of
        Nothing -> leftRight ((Name ns, removeNotFix n i ty) :) (rnfPars n i pars)
        Just 0  -> Right ((Name ns, ty) : pars)
        Just j  -> let (ns', ns'') = splitAt (j+1) ns
                   in Right ((Name ns', removeNotFix n i ty) : (Name ns'', ty) : pars)

rnfBrs :: Id -> Int -> [SBranch] -> [SBranch]
rnfBrs n i brs = [ (c, ns, if Name n `elem` ns then t else removeNotFix n i t)
                 | (c, ns, t) <- brs ]

desugarPars :: [SParam] -> [ParamV]
desugarPars pars = undefined
--    concat [zip (fromMaybe [discarded] mns) (repeat (desugar t)) | (mns, t) <- pars]

instance a ~ TermV => Desugar STerm a where
    desugar (SVar n)            = Var (Free n)
    desugar (SType l)           = Type l
    desugar (SLam pars t)       = lams (desugarPars pars) (desugar t)
    desugar (SApp t₁ t₂)        = App (desugar t₁) (desugar t₂)
    desugar (SArr pars ty)      = desugarArr pars ty
    desugar (SCase n ty brs)    =
        Case (Free n) (desugar ty) [(c, ns, desugar t) | (c, ns, t) <- brs]
    desugar (SFix nm pars ty t) = undefined
--        fix (discardedM nm) (desugarPars pars) (desugar ty) (desugar t)

desugarArr :: [SParam] -> STerm -> TermV
desugarArr []                          ty  = desugar ty
desugarArr ((Wild,        ty₁) : pars) ty₂ = arr (desugar ty₁) (desugarArr pars ty₂)
desugarArr ((Name (n:ns), ty₁) : pars) ty₂ = undefined
--    pi_ n (desugar ty₁) (desugarArr ((Just ns, ty₁) : pars) ty₂)
desugarArr ((Name [],     _)   : pars) ty  = desugarArr pars ty

class Distill a b where
    distill :: a -> b

-- instance (a ~ STerm, b ~ Id) => Distill (TermT b) a where
--     -- TODO make names unique
--     distill (Var n) = SVar n
--     distill (Type l) = SType l
--     distill (Arr ty s) =
--         SArr [(par, distill ty)] (distill (instantiate1 (Var n) s))
--       -- TODO group equal types
--       where (par, n) = case scopeVar s of
--                            Nothing -> (Nothing, discarded)
--                            Just n' -> (Just [n'], n')
--     distill (App t₁ t₂) = SApp (distill t₁) (distill t₂)
--     distill to@(Lam _ _)  =
--         let (pars, t) = go to in SLam (distillPars pars) (distill t)
--       where
--          go (Lam ty s) = let (n, t)     = freshScope s
--                              (pars, t') = go t
--                          in ((n, ty) : pars, t')
--          go t          = ([], t)
--     distill (Case v@(Var n) (CaseT s brs)) =
--         SCase n (distill (instantiate1 v s))
--               [ let (ns, s') = freshScopeNat ss i
--                 in (c, ns, distill (instantiate1 v s'))
--               | BranchT c i ss <- brs ]
--     distill (Case _ _) = error "distill: panic, got a non-var scrutined"
--     distill (Constr c tys ts) =
--         foldl1 SApp (SVar c : map distill tys ++ map distill ts)
--     distill (Fix ty tf) =
--         SFix nm pars ty' t where (nm, pars, ty', t) = distillFix ty tf

-- distillPars :: [Param] -> [SParam]
-- distillPars pars =
--     [(sequence (map fst pars'), distill ty) | pars'@((_, ty):_) <- go]
--   where
--     go = groupBy (\(mn₁, ty₁) (mn₂, ty₂) -> isJust mn₁ && isJust mn₂ && ty₁ == ty₂)
--          [(if n == discarded then Nothing else Just n, t) | (n, t) <- pars]

-- distillFix :: Term -> FixT TermT Id  -> (Maybe Id, [SParam], STerm, STerm)
-- distillFix ty (FixT i ss) =
--     -- TODO we assume that the arr is well formed
--     let Just (pars, ty') = unrollArr i ty
--         (pars', rest)    = splitAt i pars
--         nm               = scopeVar (fromScope ss)
--         ns               = [(j, n') | Name n' j <- bindings ss]
--         pars''           = mergeBi pars' ns
--     in (nm, distillPars pars'', distill (pis rest ty'),
--         distill (instantiateNatU (map (Var . fst) pars'') (Var (discardedM nm)) ss))
--   where
--     mergeBi pars ns =
--         [ (if n' == discarded then discardedM (lookup j ns) else n', ty')
--         | (j, (n', ty')) <- zip [0..] pars ]

-- freshScope :: TScope Id -> (Id, Term)
-- freshScope s = (n, instantiate1 (Var n) s)
--   where n = discardedM (scopeVar s)

-- -- INVARIANT Again, we assume that the bound 'Natural's are all below the
-- -- provided 'Natural'.
-- freshScopeNat :: (Monad f, Foldable f)
--               => Scope (TName Natural) f Id -> Natural -> ([Id], f Id)
-- freshScopeNat s i = (vars', instantiateList (map return vars') s)
--   where vars = [ (ix, n) | Name n ix <- bindings s ]
--         vars' = [ discardedM (lookup ix vars)
--                 | ix <- if i > 0 then [0..(i-1)] else [] ]
