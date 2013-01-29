{-# LANGUAGE DeriveFunctor #-}
module Kant.Syntax
    ( Id
    , IdName
    , IdRaw
    , rawId
    , ConId
    , Level
    , Module
    , Decl(..)
    , ConDecl(..)
    , Branch(..)
    , TermT(..)
    , Term
    , TermRaw
    , subst
    , unRaw
    , freshen
    ) where

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
type IdRaw = IdT ()
type Id    = IdT IdTag

rawId :: IdName -> IdRaw
rawId v = Id v ()

type ConId  = String
type Level  = Int
type Module = [Decl]

data Decl
    = Val IdName                 -- ^ Name
          Term
          [Branch]               -- ^ Branches, abstracted variables indexed by
                                 --   number, function itself is 0.
    | DataType
          Id                     -- ^ Name
          [Term]                 -- ^ Parameters' types
          Level                  -- ^ Resulting level
          [ConDecl]              -- ^ Constructors

data ConDecl = ConDecl ConId Term

data Branch = Branch ConId      -- ^ Matching a constructor
                     [Id]       -- ^ Abstracting variables
                     Term

data TermT id
    = Var (IdT id)
    | Name IdName
    | Set Level
    | App (TermT id) (TermT id)
    | Lambda (IdT id) (TermT id) (TermT id)
    deriving (Eq, Show, Functor)

type Term    = TermT IdTag
type TermRaw = TermT ()

subst :: Eq id => IdT id -> TermT id -> TermT id -> TermT id
subst v t m@(Var v')      = if v == v' then t else m
subst v t (App m n)       = App (subst v t m) (subst v t n)
subst v t (Lambda v' m n) = Lambda v' (subst v t m)
                                   (if v == v' then n else subst v t n)
subst _ _ m               = m

unRaw :: TermRaw -> Term
unRaw = go . fmap (const Nothing)
  where
    go :: TermT (Maybe IdTag) -> Term
    go (Var (Id v Nothing))     = Name v
    go (Var (Id v (Just t)))    = Var (Id v t)
    go (App m n)                = App (go m) (go n)
    go (Lambda i@(Id v _) m n)  =
        Lambda (Id v 0) (go m) (go (subst i (Var (Id v (Just 0))) n))
    go (Name n)                 = Name n
    go (Set l)                  = Set l


type Fresh a = State (Map String IdTag) a

fresh :: Id -> Fresh Id
fresh (Id v _) =
    do m <- get
       let t' = fromMaybe 0 (Map.lookup v m)
       put (Map.insert v (t' + 1) m)
       return (Id v t')

freshen :: Term -> Term
freshen t' = evalState (go t') Map.empty
  where
    go (App t m)      = App <$> go t <*> go m
    go (Lambda v t m) = do v' <- fresh v
                           Lambda v' t <$> go (subst v (Var v') m)
    go t              = return t
