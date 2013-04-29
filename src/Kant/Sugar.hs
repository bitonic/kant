module Kant.Sugar
     ( -- * Abstract syntax tree
       Id
     , Ref
     , ConId
     , SModule(..)
     , SModuleSyn
     , SModuleRef
     , SDecl(..)
     , SDeclSyn
     , SDeclRef
     , SParam
     , SConstr
     , STerm(..)
     , STermSyn
     , STermRef
     ) where

import           Kant.Term

newtype SModule r = SModule {unSModule :: [SDecl r]}
type SModuleSyn = SModule ()
type SModuleRef = SModule Ref

data SDecl r
    = SVal Id [SParam r] (STerm r) (STerm r)
    | SPostulate Id (STerm r)
    | SData ConId               -- Tycon
            [(Id, STerm r)]     -- Tycon pars
            [SConstr r]         -- Data cons
    | SRecord ConId             -- Tycon
              [(Id, STerm r)]   -- Tycon pars
              ConId             -- Datacon.
              [(Id, STerm r)]   -- Projections
    deriving (Show)
type SDeclSyn = SDecl ()
type SDeclRef = SDecl Ref

type SParam r = (Maybe Id, STerm r)
type SConstr r = (ConId, STerm r)

-- TODO add let bindings
-- | A term matching what we parse, which can be 'desugar'ed and 'distill'ed
--   into a 'Term'.
data STerm r
    = SV Id
    | STy r
    | SLam [Maybe Id] (STerm r)
    | SAnn [SParam r] (STerm r) (STerm r)
    | SApp (STerm r) (STerm r)
    | SArr [SParam r] (STerm r)
    | SHole HoleId [STerm r]
    deriving (Show)
type STermSyn = STerm ()
type STermRef = STerm Ref

