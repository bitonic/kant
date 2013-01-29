{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
-- TODO check that there are no duplicate variables
module Kant.Syntax
    ( IdT
    , IdName
    , rawId
    , ConId
    , Level
    , Module
    , DeclT(..)
    , Decl
    , BranchT(..)
    , Branch
    , TermT(..)
    , Term
    , subst
    , unRaw
    , freshen
    ) where

import           Control.Arrow (second)
import           Control.Applicative ((<$>), (<*>))
import           Data.Maybe (fromMaybe)

import           Control.Monad.State (State, get, put, evalState)

import           Data.Map (Map)
import qualified Data.Map as Map

type IdTag = Int
type IdName = String

data IdT a = Id IdName         -- ^ Original name
                a              -- ^ Tag
    deriving (Eq, Ord, Show, Functor)
type Id    = IdT IdTag

rawId :: IdName -> IdT ()
rawId v = Id v ()

type ConId  = String
type Level  = Int
type Module = [DeclT IdName]

data DeclT id
    = Val IdName                  -- ^ Name
          (TermT id)              -- ^ Type
          [BranchT id]            -- ^ Branches
    | DataType
          IdName                  -- ^ Name
          (ParamsT id)            -- ^ Parameters' types
          Level                   -- ^ Resulting level
          [(ConId, (ParamsT id))] -- ^ Constructors
    deriving (Show, Eq, Functor)
type Decl = DeclT IdTag

-- | Parameters for type and data constructors.  This is basically an arrow type
--   and in fact we could simply use a term, but I want to enforce more easily
--   the fact that the return type is either always a Setn with type
--   constructors or whatever the datatype we are defining is with data
--   constructors.
--
--   Note that each parameter is scoped through the rest of the list.  This
--   means that parameters in data constructors can shadow global parameters in
--   the type constructor.
newtype ParamsT id = Params {unParams :: [(IdT id, TermT id)]}
    deriving (Show, Eq, Functor)

data BranchT id = Branch ConId      -- ^ Matching a constructor
                         [IdT id]   -- ^ Abstracting variables
                         (TermT id)
    deriving (Show, Eq, Functor)
type Branch = BranchT IdTag

data TermT id
    = Var (IdT id)
    | Name IdName
    | Set Level
    | App (TermT id) (TermT id)
    | Lambda (IdT id) (TermT id) (TermT id)
    deriving (Eq, Show, Functor)

type Term = TermT IdTag


-- | Substuting names for terms in things.
class Subst f where
    subst :: Eq id
          => IdT id             -- ^ Substitute variable v...
          -> TermT id           -- ^ ...with term t..
          -> f id               -- ^ ...in m.
          -> f id

instance Subst TermT where
    subst v t m@(Var v')      = if v == v' then t else m
    subst v t (App m n)       = App (subst v t m) (subst v t n)
    subst v t (Lambda v' m n) = Lambda v' (subst v t m)
                                      (if v == v' then n else subst v t n)
    subst _ _ m               = m

instance Subst ParamsT where
    subst v t = Params . go . unParams
      where
        go []               = []
        go ((v', m) : rest) = (v', subst v t m) :
                              if v == v' then rest else go rest


-- | Separates Names from abstracted variables, and fills al the tags with 0s.
--   'Freshen' will later update the tags to make them unique.
class UnRaw f where
    unRaw :: f () -> f IdTag

instance UnRaw DeclT where
    unRaw (Val name t bs) = Val name (unRaw t) (map unRaw bs)
    unRaw (DataType name pars l cons) =
        DataType name (unRaw pars) l (map (second unRaw) cons)

instance UnRaw ParamsT where
    unRaw = Params . go . map (nothingT *** nothingT) . unParams
      where
        -- TODO Remove duplication between here and unMaybe
        go [] = []
        go ((i@(Id v _), t) : pars) =
            (Id v 0, unMaybe t) :
            go (unParams (subst i (Var (Id v (Just 0))) (Params pars)))

instance UnRaw BranchT where
    unRaw (Branch con vars t) =
        Branch con (map (\(Id v ()) -> Id v 0) vars) (unRaw t)

nothingT :: Functor f => f a -> f (Maybe b)
nothingT = fmap (const Nothing)

unMaybe :: TermT (Maybe IdTag) -> Term
unMaybe (Var (Id v Nothing))     = Name v
unMaybe (Var (Id v (Just t)))    = Var (Id v t)
unMaybe (App m n)                = App (unMaybe m) (unMaybe n)
unMaybe (Lambda i@(Id v _) m n)  =
    Lambda (Id v 0) (unMaybe m) (unMaybe (subst i (Var (Id v (Just 0))) n))
unMaybe (Name n)                 = Name n
unMaybe (Set l)                  = Set l

instance UnRaw TermT where
    unRaw = unMaybe . nothingT


-- | Makes sure that each abstracted variable is unique, so that there are no
--   issue with variable substitution.
class Freshen f where
    freshen' :: f IdTag -> Fresh (f IdTag)

type Fresh a = State (Map String IdTag) a

fresh :: Id -> Fresh Id
fresh (Id v _) =
    do m <- get
       let t' = fromMaybe 0 (Map.lookup v m)
       put (Map.insert v (t' + 1) m)
       return (Id v t')

instance Freshen DeclT where
    freshen' (Val name t bs) = Val name <$> freshen' t <*> mapM freshen' bs
    freshen' (DataType name pars l cons) =
        DataType name <$> freshen' pars <*> return l
                      <*> mapM (\(con, p) -> (con,) <$> freshen' p) cons

instance Freshen ParamsT where
    freshen' (Params pars') = Params <$> go pars'
      where
        -- TODO again, remove duplication between this and TermT code
        go []           = return []
        go ((v, t) : m) = do t' <- freshen' t
                             v' <- fresh v
                             ((v', t') :) <$> go m

-- Note that in the current state we don't need to freshen the constructor
-- variables, I do it anyway for consistency and because it might be a need at
-- some point.
instance Freshen BranchT where
   freshen' (Branch con vars t) = Branch con <$> mapM fresh vars <*> freshen' t

instance Freshen TermT where
    freshen' (App t m)      = App <$> freshen' t <*> freshen' m
    freshen' (Lambda v t m) = do t' <- freshen' t
                                 v' <- fresh v
                                 Lambda v' t' <$> freshen' (subst v (Var v') m)
    freshen' t              = return t

freshen :: Decl -> Decl
freshen d = evalState (freshen' d) Map.empty
