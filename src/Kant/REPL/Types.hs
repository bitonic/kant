module Kant.REPL.Types
    ( Output(..)
    ) where

import           Kant.Term

data Output
    = OTyCheck TmRefId [HoleCtx] -- Type of term
    | OPretty TmRefId            -- PPrinted term
    | OHoles [HoleCtx]
    | OOK
    | OQuit
    | OSkip
    | OHelp
