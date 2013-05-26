module Kant.Decl
    ( Cons
    , Proj
    , Projs
    , Decl(..)
    , DeclSyn
    , Module(..)
    , ModuleSyn
    ) where

import           Bound
import           Bound.Name

import           Kant.Term

type Cons r = [(ConId, TmId r)]

-- Note: we need the 'Name' just so that we can easily traverse with a 'Cursor'.
type Proj r = (Id, Scope (Name Id Int) (Tm r) Id)
type Projs r = [Proj r]

data Decl r
    = Val Id (TmId r)
    | Postulate Id (TmId r)
    | ADTD (Constr r) [Constr r]
    | RecD (Constr r)         -- Tycon
           ConId              -- Data con
           (Projs r)          -- Projections.  Note that those are all scoped
                              -- over the type con parameters, since we need
                              -- that in Elaborate.  This is ugly but necessary
                              -- due to `bound'---our datatype needs to be
                              -- uniform.
    deriving (Eq, Show)

type Constr r = (ConId, TmId r)

type DeclSyn = Decl ()

newtype Module r = Module {unModule :: [Decl r]}

type ModuleSyn = Module ()
