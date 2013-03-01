module Kant.Decl (Decl(..)) where

import           Kant.Term

data Decl
    = Val Id TermId
    | Postulate Id TermId
    | Data ConId TermId [(ConId, TermId)]
    deriving (Eq, Show)
