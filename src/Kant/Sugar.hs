module Kant.Sugar
     ( Id
     , ConId
     , Level
     , SModule(..)
     , SDecl(..)
     , SParam
     , SConstr
     , STerm(..)
     , SBranch
     ) where

import           Kant.Common

newtype SModule = SModule {unSModule :: [SDecl]}

data SDecl
    = SVal Id [SParam] STerm STerm
    | SPostulate Id STerm
    | SData ConId [SParam] Level [SConstr]

type SParam = (Maybe Id, STerm)
type SConstr = (ConId, [SParam])

data STerm
    = SVar Id
    | SType Level
    | SLam [SParam] STerm
    | SApp STerm STerm
    | SArr (Maybe Id) STerm STerm
    | SLet Id STerm STerm
    | SCase Id STerm [SBranch]

type SBranch = (ConId, [Id], STerm)
