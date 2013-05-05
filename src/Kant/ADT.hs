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
    , adtTy   :: TmRefId
    , adtRewr :: Rewr
    , adtCons :: Cons Ref
    }

data Record = Record
    { recName  :: ConId
    , recTy    :: TmRefId
    , recProjs :: [(Id, TmRefId)]
    , recRewr  :: Id -> Rewr
    }
