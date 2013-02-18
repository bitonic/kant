{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Kant.Sugar
     ( Id
     , ConId
     , Level
     , SModule(..)
     , SDecl(..)
     , SParam
     , SConstr
     , STerm(..)
     , scase
     , SBranch
     , Desugar(..)
     ) where

import           Control.Applicative ((<$))
import           Control.Arrow (second)
import           Data.Foldable (Foldable)
import           Data.List (groupBy)
import           Data.Maybe (fromMaybe, isJust)
import           Prelude hiding ((!!), length, splitAt)

import qualified Data.Set as Set

import           Bound
import           Bound.Name
import           Bound.Scope
import           Numeric.Natural

import           Kant.Common
import           Kant.Term

newtype SModule = SModule {unSModule :: [SDecl]}

data SDecl
    = SVal Id [SParam] STerm STerm
    | SPostulate Id STerm
    | SData ConId [SParam] Level [SConstr]
    deriving (Show)

type SParam = (Maybe [Id], STerm)
type SConstr = (ConId, [SParam])

data STerm
    = SVar Id
    | SType Level
    | SLam [SParam] STerm
    | SApp STerm STerm
    | SArr (Maybe Id) STerm STerm
-- TODO add this, desugaring to 'case'
--    | SLet Id STerm STerm STerm
    | SCase Id STerm [SBranch]
    | SFix (Maybe Id) [SParam] STerm STerm
    deriving (Show)

scase :: Id -> STerm -> [SBranch] -> Either Id STerm
scase n₁ ty brs =
    SCase n₁ ty brs
    <$ mapM (foldr (\n₂ se -> se >>= \s ->
                     if Set.member n₂ s then Left n₂
                     else Right (Set.insert n₂ s))
                   (Right Set.empty))
            [ns | (_, ns, _) <- brs]

type SBranch = (ConId, [Id], STerm)

class Desugar a b where
    desugar :: a -> b
    distill :: b -> a

instance a ~ Module => Desugar SModule a where
    desugar (SModule decls) = Module (map desugar decls)
    distill (Module decls)  = SModule (map distill decls)

instance a ~ Decl => Desugar SDecl a where
    -- TODO make the fix machinery more flexible, we want to be able to fix only
    -- certain arguments.
    desugar (SVal n pars ty t) =
        let pars' = desugarPars pars
            ty'   = desugar ty
        in ValD (Val n (pis pars' ty') (fix n pars' ty' (desugar t)))
    desugar (SPostulate n ty) = Postulate n (desugar ty)
    desugar (SData c pars l cons) =
        DataD (Data c (desugarPars pars) l (map (second desugarPars) cons))

    distill (ValD (Val n ty₁ (Fix ty₂ i ss))) | ty₁ == ty₂ =
        -- We assume that the name returned by 'distillFix' is 'n'
        SVal n pars ty t where (_, pars, ty, t) = distillFix ty₂ i ss
    distill (ValD (Val n ty t)) =
        SVal n [] (distill ty) (distill t)

    distill (Postulate n ty) =
        SPostulate n (distill ty)
    distill (DataD (Data c pars l cons)) =
        SData c (distillPars pars) l (map (second distillPars) cons)

desugarPars :: [SParam] -> [Param]
desugarPars pars =
    concat [zip (fromMaybe [discarded] mns) (repeat (desugar t)) | (mns, t) <- pars]

distillPars :: [Param] -> [SParam]
distillPars pars =
    [(sequence (map fst pars'), distill ty) | pars'@((_, ty):_) <- go]
  where
    go = groupBy (\(mn₁, ty₁) (mn₂, ty₂) -> isJust mn₁ && isJust mn₂ && ty₁ == ty₂)
         [(if n == discarded then Nothing else Just n, t) | (n, t) <- pars]

instance a ~ (TermT Id) => Desugar STerm a where
    desugar (SVar n)             = Var n
    desugar (SType l)            = Type l
    desugar (SLam pars t)        = lams (desugarPars pars) (desugar t)
    desugar (SApp t₁ t₂)         = App (desugar t₁) (desugar t₂)
    desugar (SArr Nothing ty t)  = arr (desugar ty) (desugar t)
    desugar (SArr (Just n) ty t) = pi_ n (desugar ty) (desugar t)
    desugar (SCase n ty brs)     =
        case_ (Var n) n (desugar ty) [(c, ns, desugar t) | (c, ns, t) <- brs]
    desugar (SFix nm pars ty t)  =
        fix (discardedM nm) (desugarPars pars) (desugar ty) (desugar t)

    -- TODO make names unique
    distill (Var n) = SVar n
    distill (Type l) = SType l
    distill (Arr ty s) =
        SArr par (distill ty) (distill (instantiate1 (Var n) s))
      where (par, n) = case scopeVar s of
                           Nothing -> (Nothing, discarded)
                           Just n' -> (Just n', n')
    distill (App t₁ t₂) = SApp (distill t₁) (distill t₂)
    distill to@(Lam _ _)  =
        let (pars, t) = go to in SLam (distillPars pars) (distill t)
      where
         go (Lam ty s) = let (n, t)     = freshScope s
                             (pars, t') = go t
                         in ((n, ty) : pars, t')
         go t          = ([], t)
    distill (Case v@(Var n) s brs) =
        SCase n (distill (instantiate1 v s))
              [ let (ns, s') = freshScopeNat ss i
                in (c, ns, distill (instantiate1 v s'))
              | (c, i, ss) <- brs ]
    distill (Case _ _ _) = error "distill: panic, got a non-var scrutined"
    distill (Constr c tys ts) =
        foldl1 SApp (SVar c : map distill tys ++ map distill ts)
    distill (Fix ty i ss) =
        let (nm, pars, ty', t) = distillFix ty i ss
        in SFix nm pars ty' t

distillFix :: Term -> Natural -> TScopeNatU Id  -> (Maybe Id, [SParam], STerm, STerm)
distillFix ty i ss =
    -- TODO we assume that the arr is well formed
    let Just (pars, ty')   = unrollArr i ty
        (pars', rest) = splitAt i pars
        nm            = scopeVar (fromScope ss)
        ns            = [(j, n') | Name n' j <- bindings ss]
        pars''        = mergeBi pars' ns
    in (nm, distillPars pars'', distill (pis rest ty'),
        distill (instantiateNatU (Var (discardedM nm)) (map (Var . fst) pars'') ss))
  where
    mergeBi pars ns =
        [ (if n' == discarded then discardedM (lookup j ns) else n', ty')
        | (j, (n', ty')) <- zip [0..] pars ]

freshScope :: TScope Id -> (Id, Term)
freshScope s = (n, instantiate1 (Var n) s)
  where n = discardedM (scopeVar s)

-- TODO this is unsafe, and relies that the 'Int' are all indeed below the bound
-- in the branch body.
freshScopeNat :: (Monad f, Foldable f)
              => Scope (TName Natural) f Id -> Natural -> ([Id], f Id)
freshScopeNat s i = (vars', instantiateList (map return vars') s)
  where vars = [ (ix, n) | Name n ix <- bindings s ]
        vars' = [ discardedM (lookup ix vars) | ix <- [0..(i-1)] ]
