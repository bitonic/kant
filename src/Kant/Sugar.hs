-- | The syntactic sugar that we actually parse.
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
     , STm(..)
     , STmSyn
     , STmRef
     ) where

import           Kant.Term

newtype SModule r = SModule {unSModule :: [SDecl r]}
type SModuleSyn = SModule ()
type SModuleRef = SModule Ref

-- | A sugared declaration.
data SDecl r
    = SVal Id [SParam r] (STm r) (STm r)
    | SPostulate Id (STm r)
    | SData ConId             -- Tycon
            [(Id, STm r)]     -- Tycon pars
            [SConstr r]       -- Data cons
    | SRecord ConId           -- Tycon
              [(Id, STm r)]   -- Tycon pars
              ConId           -- Datacon.
              [(Id, STm r)]   -- Projections
    deriving (Show)
type SDeclSyn = SDecl ()
type SDeclRef = SDecl Ref

type SParam r = (Maybe Id, STm r)
type SConstr r = (ConId, STm r)

-- TODO add let bindings
-- | A term matching what we parse, which can be 'desugar'ed and 'distill'ed
--   into a 'Tm'.
data STm r
    = SV Id
    | STy r
    | SLam [Maybe Id] (STm r)
    | SAnn [SParam r] (STm r) (STm r)
    | SApp (STm r) (STm r)
    | SArr [SParam r] (STm r)
    | SHole HoleId [STm r]
    | SEq (STm r) (STm r) (STm r) (STm r)
    | SCoeh Coeh (STm r) (STm r) (STm r) (STm r)
    | STop
    | SBot
    | SAnd (STm r) (STm r)
    | SForall [SParam r] (STm r)
    | SDec (STm r)
    | SProp r
    deriving (Show)
type STmSyn = STm ()
type STmRef = STm Ref
