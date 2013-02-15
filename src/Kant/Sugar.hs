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
     , discarded
     , Desugar(..)
     ) where

import           Control.Applicative ((<$))
import           Control.Arrow (second)
import           Data.List (groupBy)
import           Data.Maybe (fromMaybe, isJust)

import qualified Data.Set as Set

import           Bound

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

-- | A binding/pattern match that we are not going to use.
discarded :: Id
discarded = "_"

instance a ~ Module => Desugar SModule a where
    desugar (SModule decls) = Module (map desugar decls)
    distill (Module decls)  = SModule (map distill decls)

instance a ~ Decl => Desugar SDecl a where
    desugar (SVal n pars ty t) =
        let pars' = desugarPars pars
        in ValD (Val n (pis pars' (desugar ty)) (lams pars' (desugar t)))
    desugar (SPostulate n ty) = Postulate n (desugar ty)
    desugar (SData c pars l cons) =
        DataD (Data c (desugarPars pars) l (map (second desugarPars) cons))

    distill (ValD (Val no tyo to)) =
        let (pars, ty', t') = go tyo to
        in  SVal no (distillPars pars) (distill ty') (distill t')
      where
        go tyo'@(Arr ty₁ s₁) to'@(Lam ty₂ s₂) =
            if ty₁ == ty₂
            then let n = case (scopeVar s₁, scopeVar s₂) of
                             (Nothing, Nothing) -> discarded
                             (Just n', _)       -> n'
                             (_,       Just n') -> n'
                     inst = instantiate1 (Var n)
                     (pars, ty', t') = go (inst s₁) (inst s₂)
                 in ((n, ty₁) : pars, ty', t')
            else ([], tyo', to')
        go ty t = ([], ty, t)

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
    desugar (SCase n ty brs)     = case_ n (desugar ty)
                                         [(c, ns, desugar t) | (c, ns, t) <- brs]

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
    distill (Case t ty brs) = undefined
    distill (Constr c tys ts) =
        foldl1 SApp (SVar c : map distill tys ++ map distill ts)

freshScope :: TScope Id -> (Id, Term)
freshScope s = (n, instantiate1 (Var n) s)
  where n = fromMaybe discarded (scopeVar s)
