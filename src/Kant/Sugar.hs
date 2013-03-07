module Kant.Sugar
     ( -- * Abstract syntax tree
       Id
     , ConId
     , SModule(..)
     , SDecl(..)
     , SParam
     , SConstr
     , STerm(..)
     ) where

import           Kant.Term

newtype SModule = SModule {unSModule :: [SDecl]}

data SDecl
    = SVal Id [SParam] STerm STerm
    | SPostulate Id STerm
    | SData ConId [SParam] [SConstr]
    deriving (Show)

type SParam = (Maybe Id, STerm)
type SConstr = (ConId, STerm)

-- TODO add let bindings
-- | A term matching what we parse, which can be 'desugar'ed and 'distill'ed
--   into a 'Term'.
data STerm
    = SV Id
    | STy
    | SLam [Maybe Id] STerm
    | SAnn [SParam] STerm STerm
    | SApp STerm STerm
    | SArr [SParam] STerm
    | SHole HoleId [STerm]
    deriving (Show)
