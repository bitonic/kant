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
    | Data ConId (TermId r) [(ConId, TermId r)]
    deriving (Eq, Show)

type DeclSyn = Decl ()

newtype Module r = Module {unModule :: [Decl r]}

type ModuleSyn = Module ()