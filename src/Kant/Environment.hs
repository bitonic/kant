{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Sets up a warm place (cit) to reduce, typecheck, and reify things into.
--   The main hurdle is the multi-level structure of our 'Term', due to bound.
module Kant.Environment
    ( Env(..)
      -- * Utilities
    , envTy
    , envDef
    , envData'
    , newEnv
    , addAbst
    , addVal
    , addData
    ) where

import           Control.Applicative ((<$>))
import           Control.Monad (join)
import           Data.Foldable (foldr)
import           Prelude hiding (foldr)

import           Control.Monad.State (State, runState)
import           Data.Map (Map)
import qualified Data.Map as Map

import           Kant.Term

type Item = (Term, Maybe Term)

-- | Bringing it all together
data Env = Env
    { envCtx   :: Map TName Item
    , envData  :: Map ConId Data
    , envCount :: Tag
    }

-- | Looks up the type of a variable.
envTy :: Env -> TName -> Maybe Term
envTy Env{envCtx = ctx} v = fst <$> Map.lookup v ctx

-- | Looks up the body of a definition.
envDef :: Env -> TName -> Maybe Term
envDef Env{envCtx = ctx} v = join (snd <$> Map.lookup v ctx)

envData' :: Env -> TName -> Maybe Data
envData' env@Env{envData = dds} (Free n) = Map.lookup n dds
envData' _                      _        = Nothing

newEnv :: Env
newEnv = Env{ envCtx   = Map.empty
            , envData  = Map.empty
            , envCount = startTag
            }

addCtx :: Env -> TName -> Item -> Maybe Env
addCtx env@Env{envCtx = ctx} v it =
    case Map.lookup v ctx of
        Nothing -> Just (env{envCtx = Map.insert v it ctx})
        Just _  -> Nothing

-- | Adds an abstracted variable to an environment, 'Nothing' if the name is
--   already present.
addAbst :: Env -> Id -> TermV -> Maybe Env
addAbst env n t =
    addCtx env' (Free n) (t', Nothing) where (env', t') = runUniquify env t

-- | Adds a value definition to an environment, 'Nothing' if the name is already
--   present.
addVal :: Env -> Id -> TermV -> TermV -> Maybe Env
addVal env n ty t = addCtx env'' (Free n) (ty', (Just t'))
  where (env', ty') = runUniquify env ty
        (env'', t') = runUniquify env' t

-- | Extracts the types out of a data declaration.
--
--   A type function will be generated as type constructor, taking the
--   parameters as arguments and returning someting of @Type l@, where @l@ is
--   the level specified in the declaration.
--
--   Another function will be generated for each data constructor, taking all
--   the parameters of the type constructor plus its own parameter.
dataDecl :: Data -> State Tag ((Id, Item), [(Id, Item)])
dataDecl (Data c pars l cons) =
    do cons' <- sequence [ do f <- conFun c' pars'
                              return (c', (arrs (pars ++ pars') resTy, Just f))
                         | (c', pars') <- cons ]
       return ((c, (arrs pars (Type l), Nothing)), cons')
  where
    resTy = app (Var (Free c) : map snd pars)
    conFun = undefined
    -- conFun c' pars' =
    --     let ref = zip (map (("_"++) . show) [(0::Natural)..]) (map snd pars')
    --     in lams (pars ++ ref)
    --             (Constr c' (map (Var . fst) pars) (map (Var . fst) ref))

-- | Adds the type constructors and the data declarations as abstracted variable
--   to an environment, @'Left' n@ if name @n@ is already present.
addData :: Env -> DataV -> Either ConId Env
addData env@Env{envData = dds} ddo =
    do env₂ <- if Map.member c₁ dds
               then Left c₁
               else Right (env₁{envData = Map.insert c₁ dd dds})
       let (env₃, (tyc, cons)) = runUniquify' env₂ (dataDecl dd)
       foldr (\(c₂, item) enve ->
               do env₄ <- enve;
                  maybe (Left c₂) Right (addCtx env₄ (Free c₂) item))
             (Right env₃) (tyc : cons)
  where (env₁, dd@(Data c₁ _ _ _)) = runUniquify env ddo

-----

class Uniquify f where
    uniquify :: f Void Id -> State Tag (f Id Tag)

instance Uniquify TermT

instance Uniquify DataT

runUniquify' :: Env -> State Tag a -> (Env, a)
runUniquify' env@Env{envCount = ta} s = (env{envCount = ta'}, x)
  where (x, ta') = runState s ta

runUniquify :: Uniquify f => Env -> f Void Id -> (Env, f Id Tag)
runUniquify env x = runUniquify' env (uniquify x)
