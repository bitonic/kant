module Kant.REPL.Types
    ( Output(..)
    ) where

import           Kant.Term
import           Kant.Env

data Output
    = OTyCheck TmRefId [HoleCtx] -- Type of term
    | OPretty TmRefId            -- PPrinted term
    | OInfo Free
    | OHoles [HoleCtx]
    | OOK
    | OQuit
    | OSkip
    | OHelp
