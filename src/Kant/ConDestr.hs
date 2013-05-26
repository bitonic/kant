{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.ConDestr (conDestr, conDestrDecl, conDestrModule) where

import           Bound
import           Data.Proxy

import           Kant.ADT
import           Kant.Common
import           Kant.Cursor
import           Kant.Decl
import           Kant.Env
import           Kant.Term
#include "../impossible.h"

conDestr :: (VarC v) => EnvP v -> Tm r v -> Either Id (Tm r v)
conDestr env (appV -> (V v, ts)) =
    do ts' <- mapM (conDestr env) ts
       case free' env v of
           Nothing -> return (app (V v : ts'))
           Just dc ->
               case lookupFree env dc of
                   Nothing -> return (app (V v : ts'))
                   Just f  -> do (t, ts'') <- f ts'
                                 return (app (t : ts''))
conDestr _ (V v) = return (V v)
conDestr _ (Ty r) = return (Ty r)
conDestr env (Lam s) = Lam . toScope <$> conDestr (nestP env) (fromScope s)
conDestr env (Arr ty s) =
    Arr <$> conDestr env ty <*> (toScope <$> conDestr (nestP env) (fromScope s))
conDestr env (App t₁ t₂) = App <$> conDestr env t₁ <*> conDestr env t₂
conDestr env (Ann ty t) = Ann <$> conDestr env ty <*> conDestr env t
conDestr env (Hole hid ts) = Hole hid <$> mapM (conDestr env) ts
conDestr _ _ = IMPOSSIBLE("we shouldn't have constructors/destructors now")

-- TODO eliminate duplication between here and 'putRef'
conDestrDecl :: EnvP Id -> Decl r -> Either Id (Decl r)
conDestrDecl env (Val n t)             = Val n <$> conDestr env t
conDestrDecl env (Postulate n ty)      = Postulate n <$> conDestr env ty
conDestrDecl env (ADTD (tyc, tycty) cons) =
    do tycty' <- conDestr env tycty
       ADTD (tyc, tycty') <$> mapM (\(dc, dcty) -> (dc,) <$> conDestr env dcty) cons
conDestrDecl env (RecD (tyc, tycty) dc projs) =
    do tycty' <- conDestr env tycty
       let env' = nestC env (const Proxy)
       RecD (tyc, tycty') dc <$>
           mapM (\(pr, prty) -> (pr,) <$> (toScope <$> conDestr env' (fromScope prty)))
                projs

conDestrModule :: EnvP Id -> Module r -> Either Id (Module r)
conDestrModule env (Module decls) = Module <$> mapM (conDestrDecl env) decls

lookupFree :: Env f v -> Id -> Maybe ([Tm r v] -> Either Id (Tm r v, [Tm r v]))
lookupFree env n =
    do fr <- envFree env n
       case fr of
           DataCon tyc ->
               let adt = envADT env tyc
                   ty  = case lookup n (adtCons adt) of
                       Nothing  -> IMPOSSIBLE("Non-existant datacon " ++ n)
                       Just ty' -> ty'
               in Just (dataCon ADT_ tyc ty)
           DataElim tyc -> Just (destr ADT_ tyc)
           RecCon tyc ->
               -- TODO we could assert that the data constructor is the
               -- right one here.
               let rec = envRec env tyc
               in Just (dataCon Rec_ tyc (snd (recCon rec)))
           RecProj tyc -> Just (destr Rec_ tyc)
           _ -> Nothing
  where
    dataCon ar tyc ty ts =
        let pars = arrLen ty
            (ts₁, ts₂) = splitAt (arrLen ty) ts
        in if length ts >= pars then Right (Con ar tyc n ts₁, ts₂) else Left n

    destr ar tyc (t : ts) = Right (Destr ar tyc n t, ts)
    destr _  _   []       = Left n

nestP :: EnvP v -> EnvP (Var NameId v)
nestP = (`nestC` const Proxy)
