{-# LANGUAGE RankNTypes #-}
-- | A reified representation of abstract data types.
module Kant.ADT
    ( Rewr
    , ADT(..)
    , Record(..)
    ) where

import           Kant.Decl
import           Kant.Term

type Rewr = forall v. VarC v => [TmRef v] -> Maybe (TmRef v)

-- | The difference between this and a 'Kant.Decl' is that the constructors are
--   checked for well formedness.  Moreover, the 'Rewrite'.
data ADT = ADT
    { adtName :: ConId
    , adtTy   :: TmRefId        -- ^ Type of the tycon
    , adtElim :: TmRefId        -- ^ Type of the eliminator
    , adtRewr :: Rewr           -- ^ Rewrite rule for the eliminator
    , adtCons :: Cons Ref       -- ^ Constructor types
    }

data Record = Record
    { recName  :: ConId
    , recTy    :: TmRefId          -- ^ Type of the tycon
    , recCon   :: (ConId, TmRefId) -- ^ Constructor
    , recProjs :: [(Id, TmRefId)]  -- ^ Types of the projections
    , recRewr  :: Id -> Rewr       -- ^ Rewrite rules for the projections
    }
