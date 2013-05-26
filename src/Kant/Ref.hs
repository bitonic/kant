{-# LANGUAGE TypeFamilies #-}
module Kant.Ref (PutRef(..)) where

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
    putRef = mapDecl putRef

instance r ~ () => PutRef (Module r) where
    type WithRef (Module r) = Module Ref
    putRef (Module m) = Module <$> mapM putRef m
