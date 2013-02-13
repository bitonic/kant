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

import           Control.Arrow ((***))
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

data DesugarError
    = RepeatedVariable Id

class Desugar a b where
    desugar :: a -> Either DesugarError b
    distill :: b -> a

instance Desugar SDecl Decl where
    desugar (SVal n pars ty t) = undefined
    desugar (SPostulate n ty) = undefined
    desugar (SData c pars l cons) = undefined

    distill (ValD (Val n ty t)) = undefined
    distill (Postulate n ty) = undefined
    distill (DataD (Data c pars l cons)) = undefined

instance Desugar STerm (TermT Id) where
    desugar (SVar n)         = undefined
    desugar (SType l)        = return (Type l)
    desugar (SLam pars t)    = undefined
    desugar (SApp t₁ t₂)     = undefined
    desugar (SArr mn ty t)   = undefined
    desugar (SCase n ty brs) = undefined

    distill (Var n) = undefined
    distill (Type l) = SType l
    distill (App t₁ t₂) = undefined
    distill (Lam ty t)  = undefined
    distill (Case t ty brs) = undefined
    distill (Constr c tys ts) = undefined

