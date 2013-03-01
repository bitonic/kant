module Kant.Decl (Decl(..), Module(..)) where

import           Kant.Term

data Decl
    = Val Id TermId
    | Postulate Id TermId
    | Data ConId TermId [(ConId, TermId)]
    deriving (Eq, Show)

newtype Module = Module {unModule :: [Decl]}