{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
module Kant.Decl
    ( Cons
    , Projs
    , Decl(..)
    , DeclSyn
    , Module(..)
    , ModuleSyn
    , mapDecl
    ) where

import           Bound

import           Kant.Term
import           Kant.Common

type Cons r = [(ConId, TmId r)]
type Projs r = [(Id, Scope Int (Tm r) Id)]

data Decl r
    = Val Id (TmId r)
    | Postulate Id (TmId r)
    | ADTD (Constr r) [Constr r]
    | RecD (Constr r)         -- Tycon
           ConId              -- Data con
           (Projs r)          -- Projections.  Note that those are all scoped
                              -- over the type con parameters, since we need
                              -- that in Elaborate.  This is ugly but necessary
                              -- due to `bound'---our datatype needs to be
                              -- uniform.
    deriving (Eq, Show)

type Constr r = (ConId, TmId r)

type DeclSyn = Decl ()

newtype Module r = Module {unModule :: [Decl r]}

type ModuleSyn = Module ()

mapDecl :: Monad m => (forall v. Tm r₁ v -> m (Tm r₂ v)) -> Decl r₁ -> m (Decl r₂)
mapDecl f (Val n t)             = Val n <$> f t
mapDecl f (Postulate n ty)      = Postulate n <$> f ty
mapDecl f (ADTD (tyc, tycty) cons) =
    do tycty' <- f tycty
       ADTD (tyc, tycty') <$> mapM (\(dc, dcty) -> (dc,) <$> f dcty) cons
mapDecl f (RecD (tyc, tycty) dc projs) =
    do tycty' <- f tycty
       RecD (tyc, tycty') dc <$>
           mapM (\(pr, prty) -> (pr,) <$> (toScope <$> f (fromScope prty)))
           projs

