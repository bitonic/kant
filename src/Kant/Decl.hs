module Kant.Decl
    ( Cons
    , Decl(..)
    , DeclSyn
    , Module(..)
    , ModuleSyn
    ) where

import           Kant.Term

type Cons r = [(ConId, TermId r)]

data Decl r
    = Val Id (TermId r)
    | Postulate Id (TermId r)
    | Data (Constr r) [Constr r]
    | Record (Constr r)         -- Tycon
             ConId              -- Data con
             [(Id, TermId r)]   -- Projections
    deriving (Eq, Show)

type Constr r = (ConId, TermId r)

type DeclSyn = Decl ()

newtype Module r = Module {unModule :: [Decl r]}

type ModuleSyn = Module ()
