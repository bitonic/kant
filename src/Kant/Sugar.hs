{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
     ) where

import           Control.Arrow ((***), second)
import           Control.Applicative ((<$))
import           Data.Maybe (fromMaybe)

import qualified Data.Set as Set

import           Kant.Common
import           Kant.Term

newtype SModule = SModule {unSModule :: [SDecl]}

data SDecl
    = SVal Id [SParam] STerm STerm
    | SPostulate Id STerm
    | SData ConId [SParam] Level [SConstr]

type SParam = (Maybe Id, STerm)
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

instance Desugar SDecl Decl where
    desugar (SVal n pars ty t) =
        let pars' = desugarPars pars
        in ValD (Val n (pis pars' (desugar ty)) (lams pars' (desugar t)))
    desugar (SPostulate n ty) = Postulate n (desugar ty)
    desugar (SData c pars l cons) =
        DataD (Data c (desugarPars pars) l (map (second desugarPars) cons))

    distill (ValD (Val n ty t)) = undefined
    distill (Postulate n ty) = undefined
    distill (DataD (Data c pars l cons)) = undefined

desugarPars :: [SParam] -> [Param]
desugarPars = map (fromMaybe discarded *** desugar)

instance Desugar STerm (TermT Id) where
    desugar (SVar n)             = Var n
    desugar (SType l)            = Type l
    desugar (SLam pars t)        = lams (desugarPars pars) (desugar t)
    desugar (SApp t₁ t₂)         = App (desugar t₁) (desugar t₂)
    desugar (SArr Nothing ty t)  = arr (desugar ty) (desugar t)
    desugar (SArr (Just n) ty t) = pi_ n (desugar ty) (desugar t)
    desugar (SCase n ty brs)     = case_ n (desugar ty)
                                         [(c, ns, desugar t) | (c, ns, t) <- brs]

    distill (Var n) = undefined
    distill (Type l) = SType l
    distill (App t₁ t₂) = undefined
    distill (Lam ty t)  = undefined
    distill (Case t ty brs) = undefined
    distill (Constr c tys ts) = undefined

