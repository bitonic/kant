{-# LANGUAGE RankNTypes #-}
-- | A reified representation of abstract data types---we store this in the
--   environment.
module Kant.ADT
    ( Rewr_
    , ADT(..)
    , Rec(..)
    ) where

import           Kant.Decl
import           Kant.Term

-- | A rewriting rule: takes a term on which the rewriting will depend on (for
--   example a record we are projecting from or an ADT we are destructing), a
--   list of "arguments", and maybe reduces to some other arguments.
type Rewr_ = forall v. VarC v => TmRef v -> [TmRef v] -> Maybe [TmRef v]

data ADT = ADT
    { adtName :: ConId
    , adtTy   :: TmRefId       -- ^ Type of the tycon
    , adtElim :: TmRefId       -- ^ Type of the eliminator
    , adtRewr :: Rewr_         -- ^ Rewrite rule for the eliminator
    , adtCons :: [Constr Ref]  -- ^ Constructor types
    }

data Rec = Rec
    { recName  :: ConId
    , recTy    :: TmRefId          -- ^ Type of the tycon
    , recCon   :: Constr Ref       -- ^ Constructor
    , recProjs :: [(Id, TmRefId)]  -- ^ Types of the projections
    , recRewr  :: Id -> Rewr_      -- ^ Rewrite rules for the projections
    }
