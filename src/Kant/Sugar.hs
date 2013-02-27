{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.Sugar
     ( -- * Abstract syntax tree
       Id
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
     , buildVal
       -- * Desugaring
     , desugar
       -- * Distilling
     , distill
     ) where

import           Control.Applicative ((<$))
import           Control.Arrow (first, second, (+++))
import           Data.List (groupBy, elemIndex)
import           Data.Maybe (fromMaybe)

import qualified Data.Set as Set

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
    | SCase STerm (Maybe Id) STerm [SBranch]
    | SFix (Maybe Id) [SParam] STerm STerm
    deriving (Show)

-- | Checks that all variables matched in branches are distinct.  Returns
--   @'Left' v@ if `v' is duplicate somewhere.
scase :: STerm -> Maybe Id -> STerm -> [SBranch] -> Either Id STerm
scase t n₁ ty brs =
    SCase t n₁ ty brs
    <$ mapM (foldr (\b se -> se >>= \s ->
                     case b of
                         Nothing -> Right s
                         Just n₂ | Set.member n₂ s -> Left n₂
                         Just n₂ -> Right (Set.insert n₂ s))
                   (Right Set.empty))
            [ns | (_, ns, _) <- brs]

type SBranch = ( ConId         -- Constructor
               , [Maybe Id]    -- Matched variables
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
        dataD c (desugarPars pars) l (map (second desugarPars) cons)

buildVal :: Id -> SValParams -> STerm -> STerm -> STerm
buildVal n (SValParams pars mfpars) ty t =
    SLam pars $
    case mfpars of
        Just fpars -> SFix (Just n) fpars ty (removeNotFix n i t)
        Nothing    -> t
  where i = sum (map (maybe 1 length . fst) pars)

unrollSApp :: STerm -> [STerm]
unrollSApp (SApp t₁ t₂) = unrollSApp t₁ ++ [t₂]
unrollSApp t₁           = [t₁]

removeNotFix :: Id -> Int -> STerm -> STerm
removeNotFix _ _ t@(SVar _) = t
removeNotFix _ _ t@(SType _) = t
removeNotFix n i (SLam pars t) =
    case rnfPars n i pars of
        Left pars'  -> SLam pars' (removeNotFix n i t)
        Right pars' -> SLam pars' t
removeNotFix n₁ i (unrollSApp -> (SVar n₂ : ts)) | n₁ == n₂ =
    -- TODO emit an error if the application has less than `i' things
    foldl SApp (SVar n₂) (drop i (map (removeNotFix n₁ i) ts))
removeNotFix n i (SApp t₁ t₂) = SApp (removeNotFix n i t₁) (removeNotFix n i t₂)
removeNotFix n i (SArr pars t) =
    case rnfPars n i pars of
        Left pars'  -> SArr pars' (removeNotFix n i t)
        Right pars' -> SArr pars' t
removeNotFix n₁ i (SCase t n₂ ty brs) =
    SCase t n₂ (removeNotFix n₁ i ty) (rnfBrs n₁ i brs)
removeNotFix n₁ _ t@(SFix (Just n₂) _ _ _) | n₁ == n₂ = t
removeNotFix n i (SFix nm pars ty t) =
    case rnfPars n i pars of
        Left pars'  -> SFix nm pars' (removeNotFix n i ty) (removeNotFix n i t)
        Right pars' -> SFix nm pars' ty t

leftRight :: (a -> b) -> Either a a -> Either b b
leftRight f = f +++ f

rnfPars :: Id -> Int -> [SParam] -> Either [SParam] [SParam]
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

rnfBrs :: Id -> Int -> [SBranch] -> [SBranch]
rnfBrs n i brs = [ (c, ns, if Just n `elem` ns then t else removeNotFix n i t)
                 | (c, ns, t) <- brs ]

desugarPars :: [SParam] -> [(Id, TermV)]
desugarPars pars =
    concat [zip (fromMaybe [discard] mns) (repeat (desugar t)) | (mns, t) <- pars]

instance (a ~ TermV) => Desugar STerm a where
    desugar (SVar n)            = Var n
    desugar (SType l)           = Type l
    desugar (SLam pars t)       = lams (desugarPars pars) (desugar t)
    desugar (SApp t₁ t₂)        = App (desugar t₁) (desugar t₂)
    desugar (SArr pars ty)      = desugarArr pars ty
    desugar (SCase t n ty brs)  =
        case_ (desugar t) (elimMaybe n) (desugar ty)
              [(c, map elimMaybe ns, desugar t') | (c, ns, t') <- brs]
    desugar (SFix b pars ty t) =
        fix (desugarPars pars) (desugar ty) (elimMaybe b) (desugar t)

desugarArr :: [SParam] -> STerm -> TermV
desugarArr []                          ty  = desugar ty
desugarArr ((Nothing,     ty₁) : pars) ty₂ = arr (desugar ty₁) (desugarArr pars ty₂)
desugarArr ((Just (n:ns), ty₁) : pars) ty₂ =
    pi_ (desugar ty₁) n (desugarArr ((Just ns, ty₁) : pars) ty₂)
desugarArr ((Just [],     _)   : pars) ty  = desugarArr pars ty

ifOccurs :: Id -> TermV -> Maybe Id
ifOccurs v t = if occurs v t then Just v else Nothing

class Distill a b where
    distill :: a -> b

instance (a ~ STerm, v ~ Id) => Distill (TermT v) a where
    distill (Var n) = SVar n
    distill (Type l) = SType l
    distill to@(Arr _) =
        let (pars, ty) = go to in SArr (distillPars pars) (distill ty)
      where
        go (Arr (Abs ty (Scope b t))) = first ((ifOccurs b t, ty):) (go t)
        go t                          = ([], t)
    distill (App t₁ t₂) = SApp (distill t₁) (distill t₂)
    distill to@(Lam _)  =
        let (pars, t) = go to in SLam (distillPars pars) (distill t)
      where
         go (Lam (Abs ty (Scope b t))) = first ((ifOccurs b t, ty):) (go t)
         go t                          = ([], t)
    distill (Case t (Scope b ty) brs) =
        SCase (distill t) (ifOccurs b ty) (distill ty)
              [(c, map Just bs, distill t') | (c, Tele (branchBs -> bs) t') <- brs]
    distill (Constr c tys ts) =
        foldl1 SApp (SVar c : map distill tys ++ map distill ts)
    distill (Fix (Tele pars (Abs ty (Scope b t)))) =
        -- TODO discard unused things in the pars
        SFix (ifOccurs b t)
             (distillPars (map (first Just) pars)) (distill ty) (distill t)

distillPars :: [(Maybe Id, TermV)] -> [(Maybe [Id], STerm)]
distillPars pars =
    [(sequence (map fst pars'), distill ty) | pars'@((_, ty):_) <- go]
  where
    go = groupBy (\(_, ty₁) (_, ty₂) -> ty₁ == ty₂) pars

elimMaybe :: Maybe Id -> Id
elimMaybe Nothing  = discard
elimMaybe (Just n) = n
