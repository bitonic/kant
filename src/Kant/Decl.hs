-- | Syntax for declarations.
module Kant.Decl
    ( Constr
    , Proj
    , Decl(..)
    , DeclSyn
    , Module(..)
    , ModuleSyn
    ) where

import           Bound
import           Bound.Name

import           Kant.Term

-- | A constructor of some kind.  The term part will be some sort of telescope.
type Constr r = (ConId, TmId r)

-- TODO this is inconsistent with 'Constr': why don't we scope the tycon
-- parameters there too?
-- | A projection, scoped over the type parameters of the tycon.
--
--   Note: we need the 'Name' just so that we can easily traverse with a 'Cursor'.
type Proj r = (Id, Scope (Name Id Int) (Tm r) Id)

-- | Declarations
data Decl r
    = Val Id (TmId r)           -- ^ Declared value: type and body.
    | Postulate Id (TmId r)     -- ^ Postulated variable: only type.  ^
      --   Abstract data type: a 'Constr' for the tycon, a list of 'Cosntr's
      --   for the datacon.
    | ADTD (Constr r) [Constr r]
      -- ^ Records: a 'Constr' for the tycon, a 'ConId' for the datacon, a
      --   list of 'Proj's for the projections.
    | RecD (Constr r)         -- Tycon
           ConId              -- Data con
           [Proj r]           -- Projections.  Note that those are all scoped
                              -- over the type con parameters, since we need
                              -- that in Elaborate.  This is ugly but necessary
                              -- due to `bound'---our datatype needs to be
                              -- uniform.
    deriving (Eq, Show)

type DeclSyn = Decl ()

-- | A 'Module' is a list of 'Decl's.
newtype Module r = Module {unModule :: [Decl r]}

type ModuleSyn = Module ()
