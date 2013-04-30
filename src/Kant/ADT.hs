{-# LANGUAGE RankNTypes #-}
-- | A reified representation of abstract data types.
module Kant.ADT (Rewr, ADT(..), Record(..)) where

import           Kant.Decl
import           Kant.Term

type Rewr = forall v. VarC v => [TermRef v] -> Maybe (TermRef v)

-- | The difference between this and a 'Kant.Decl' is that the constructors are
--   checked for well formedness.  Moreover, the 'Rewrite'.
data ADT = ADT
    { adtName :: ConId
    , adtTy   :: TermRefId
    , adtRewr :: Rewr
    , adtCons :: Cons Ref
    }

data Record = Record
    { recName  :: ConId
    , recTy    :: TermRefId
    , recProjs :: [(Id, TermRefId)]
    , recRewr  :: Id -> Rewr
    }

