{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
module Kant.Ref (PutRef(..)) where

import           Control.Applicative ((<$>), (<*>))

import           Control.Monad.State (State, StateT, runState, get, put)

import           Kant.Term
import           Kant.Env
import           Kant.Decl

class PutRef a where
    type WithRef a :: *
    putRef :: EnvId -> a -> (EnvId, WithRef a)

freshRef :: Monad m => StateT EnvId m Ref
freshRef =
    do env@Env{envRef = r} <- get
       put env {envRef = r + 1}
       return r

putTerm :: Term () v -> State EnvId (TermRef v)
putTerm = mapRef (const freshRef)

runFresh :: EnvId -> State EnvId a -> (EnvId, a)
runFresh env₁ s = (env₂, t) where (t, env₂) = runState s env₁

instance r ~ () => PutRef (Term r v) where
    type WithRef (Term r v) = TermRef v
    putRef env = runFresh env . putTerm

putDecl :: Decl () -> State EnvId (Decl Ref)
putDecl (Val n t)             = Val n <$> putTerm t
putDecl (Postulate n ty)      = Postulate n <$> putTerm ty
putDecl (Data tyc tycty cons) =
    Data tyc <$> putTerm tycty
             <*> mapM (\(dc, dcty) -> (dc,) <$> putTerm dcty) cons

instance r ~ () => PutRef (Decl r) where
    type WithRef (Decl r) = Decl Ref
    putRef env = runFresh env . putDecl

instance r ~ () => PutRef (Module r) where
    type WithRef (Module r) = Module Ref
    putRef env (Module m) = runFresh env (Module <$> mapM putDecl m)
