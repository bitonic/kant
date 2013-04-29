{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
module Kant.Ref (PutRef(..)) where

import           Kant.Common
import           Kant.Decl
import           Kant.Monad
import           Kant.Term

class PutRef a where
    type WithRef a :: *
    putRef :: Monad m => a -> KMonadE f v m (WithRef a)

instance r ~ () => PutRef (Term r v) where
    type WithRef (Term r v) = TermRef v
    putRef = mapRef (const freshRef)

instance r ~ () => PutRef (Decl r) where
    type WithRef (Decl r) = Decl Ref
    putRef (Val n t)             = Val n <$> putRef t
    putRef (Postulate n ty)      = Postulate n <$> putRef ty
    putRef (Data (tyc, tycty) cons) =
        do tycty' <- putRef tycty
           Data (tyc, tycty') <$> mapM (\(dc, dcty) -> (dc,) <$> putRef dcty) cons

instance r ~ () => PutRef (Module r) where
    type WithRef (Module r) = Module Ref
    putRef (Module m) = Module <$> mapM putRef m
