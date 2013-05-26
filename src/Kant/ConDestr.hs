{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Kant.ConDestr (conDestr) where

import           Bound
import           Data.Proxy

import           Kant.Common
import           Kant.Cursor
import           Kant.Env
import           Kant.Term
#include "../impossible.h"

conDestr :: (VarC v) => EnvP v -> Tm r v -> Either Id (Tm r v)
conDestr env (appV -> (V v, ts)) =
    do ts' <- mapM (conDestr env) ts
       case free' env v of
           Nothing -> return (app (V v : ts'))
           Just dc ->
               case lookupDataCon env dc of
                   Nothing -> return (app (V v : ts'))
                   Just (ar, tyc, n) | length ts >= n ->
                       let (ts₁, ts₂) = splitAt n ts'
                       in return (app (Con ar tyc dc ts₁ : ts₂))
                   Just _ -> Left dc
conDestr _ (V v) = return (V v)
conDestr _ (Ty r) = return (Ty r)
conDestr env (Lam s) = Lam . toScope <$> conDestr (nestC env Proxy) (fromScope s)
conDestr env (Arr ty s) =
    Arr <$> conDestr env ty <*> (toScope <$> conDestr (nestC env Proxy) (fromScope s))
conDestr env (App t₁ t₂) = App <$> conDestr env t₁ <*> conDestr env t₂
conDestr env (Hole hid ts) = Hole hid <$> mapM (conDestr env) ts
conDestr _ _ = IMPOSSIBLE("we shouldn't have constructors/destructors now")

lookupDataCon :: Env f v -> Id -> Maybe (ADTRec, ConId, Int)
lookupDataCon = undefined
