{-# LANGUAGE TypeFamilies #-}
module Kant.Ref (PutRef(..)) where

import           Kant.Term
import           Kant.Env
import           Kant.Decl
import           Kant.TyCheck

class PutRef a where
    type WithRef a :: *
    putRef :: MonadTyCheck m => EnvId -> a -> m (EnvId, WithRef a)

instance r ~ () => PutRef (Term r v) where
    type WithRef (Term r v) = TermRef v
    putRef env t = undefined

instance r ~ () => PutRef (Decl r) where
    type WithRef (Decl r) = Decl FRef
    putRef env d = undefined

instance r ~ () => PutRef (Module r) where
    type WithRef (Module r) = Module FRef
    putRef env d = undefined
