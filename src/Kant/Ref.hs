{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
module Kant.Ref (PutRef(..)) where

import           Bound

import           Kant.Common
import           Kant.Decl
import           Kant.Monad
import           Kant.Term

class PutRef a where
    type WithRef a :: *
    putRef :: Monad m => a -> KMonadE f v m (WithRef a)

instance r ~ () => PutRef (Tm r v) where
    type WithRef (Tm r v) = TmRef v
    putRef = mapRef (const freshRef)

instance r ~ () => PutRef (Decl r) where
    type WithRef (Decl r) = Decl Ref
    putRef (Val n t)             = Val n <$> putRef t
    putRef (Postulate n ty)      = Postulate n <$> putRef ty
    putRef (ADTD (tyc, tycty) cons) =
        do tycty' <- putRef tycty
           ADTD (tyc, tycty') <$> mapM (\(dc, dcty) -> (dc,) <$> putRef dcty) cons
    putRef (RecD (tyc, tycty) dc projs) =
        do tycty' <- putRef tycty
           RecD (tyc, tycty') dc <$>
               mapM (\(pr, prty) -> (pr,) <$> (toScope <$> putRef (fromScope prty)))
                    projs

instance r ~ () => PutRef (Module r) where
    type WithRef (Module r) = Module Ref
    putRef (Module m) = Module <$> mapM putRef m
