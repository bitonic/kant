{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Kant.Syntax where

import           Control.Applicative (Applicative(..))
import           Control.Arrow (second)
import           Control.Monad (ap)
import           Data.Foldable (Foldable)
import           Data.Traversable (Traversable)

import           Bound
import           Bound.Name
import           Prelude.Extras


type Id     = String
type ConId  = String
type Module = [Id]
type Level  = Int
data QName  = QName Module Id

type ScopeInt t a = Scope (Name Id Int) t a
type ScopeIntId t = ScopeInt t Id
type ScopeUnit t a = Scope (Name Id ()) t a

data Decl
    = Val Id                     -- ^ Name
          (Term Id)              -- ^ Type
          (ScopeIntId Term)      -- ^ Body, abstracted variables indexed by number,
                                 --   function itself is 0.
    | DataType
          Id                     -- ^ Name
          [TermId]               -- ^ Parameters' types
          Level                  -- ^ Resulting level
          [ScopeIntId ConDecl]   -- ^ The constructors.  Again, parameters by
                                 --   number, type constructor itself is 0.

data ConDecl a = ConDecl ConId [Term a]

data Term a
    = Var a
    | App (Term a) (Term a)
    | Con ConId
    | Case (Term a) [CaseBranch a]
    | Set Level
    | Lambda (Term a)           -- ^ Type of the argument
             (ScopeUnit Term a)
    deriving (Eq, Ord, Show, Read, Functor, Foldable, Traversable)

-- | Yet again, variables abstracted by the pattern are indexed by number.
type CaseBranch a = (ConId, (ScopeInt Term a))

type TermId = Term Id

instance Eq1 Term   where (==#)      = (==)
instance Ord1 Term  where compare1   = compare
instance Show1 Term where showsPrec1 = showsPrec
instance Read1 Term where readsPrec1 = readsPrec
instance Applicative Term where pure = Var; (<*>) = ap

instance Monad Term where
    return = Var

    Var v       >>= f = f v
    App t m     >>= f = App (t >>= f) (m >>= f)
    Con ci      >>= _ = Con ci
    Case t bs   >>= f = Case (t >>= f) (map (second (>>>= f)) bs)
    Set l       >>= _ = Set l
    Lambda ty t >>= f = Lambda (ty >>= f) (t >>>= f)

