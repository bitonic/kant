module Kant.Syntax where

import           Bound
import           Bound.Name

type Id     = String
type ConId  = String
type Module = [Id]
type Level  = Int
data QName  = QName Module Id

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
    = Var Id
    | App (Term a) (Term a)
    | Con ConId
    | Case (Term a) [CaseBranch a]
    | Set Level
    | Lambda (Term a)           -- ^ Type of the argument
             (ScopeUnit Term a)

-- | Yet again, variables abstracted by the pattern are indexed by number.
type CaseBranch a = (ConId, (ScopeInt Term a))

type TermId = Term Id
type ScopeInt t a = Scope (Name Id Int) t a
type ScopeIntId t = ScopeInt t Id
type ScopeUnit t a = Scope (Name Id ()) t a
