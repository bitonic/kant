module Kant.Decl
    ( Cons
    , Projs
    , Decl(..)
    , DeclSyn
    , Module(..)
    , ModuleSyn
    ) where

import           Kant.Term

type Cons r = [(ConId, TermId r)]
type Projs r = [(Id, TermId r)]

data Decl r
    = Val Id (TermId r)
    | Postulate Id (TermId r)
    | ADTD (Constr r) [Constr r]
    | RecD (Constr r)         -- Tycon
           ConId              -- Data con
           (Projs r)          -- Projections.  Note that those are all scoped
                              -- over the type con parameters, since we need
                              -- that in Elaborate.  This is ugly but necessary
                              -- due to `bound'---our datatype needs to be
                              -- uniform.
    deriving (Eq, Show)

type Constr r = (ConId, TermId r)

type DeclSyn = Decl ()

newtype Module r = Module {unModule :: [Decl r]}

type ModuleSyn = Module ()
