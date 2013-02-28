module Kant.Sugar
     ( -- * Abstract syntax tree
       Id
     , ConId
     , Level
     , SModule(..)
     , SDecl(..)
     , SParam
     , SConstr
     , STerm(..)
     ) where

import           Kant.Term

newtype SModule = SModule {unSModule :: [SDecl]}

data SDecl
    = SVal Id [SParam] STerm
    | SPostulate Id STerm
    | SData ConId [SParam] Level [SConstr]
    deriving (Show)

type SParam = (Maybe [Id], STerm)
type SConstr = (ConId, [SParam])

-- TODO add let bindings
-- | A term matching what we parse, which can be 'desugar'ed and 'distill'ed
--   into a 'Term'.
data STerm
    = SV Id
    | STy Level
    | SLam [SParam] STerm
    | SApp STerm STerm
    | SArr [SParam] STerm
    deriving (Show)
