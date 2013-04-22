module Kant.REPL.Types
    ( Output(..)
    ) where

import           Kant.Term

data Output
    = OTyCheck TermRefId [HoleCtx] -- Type of term
    | OPretty TermRefId            -- PPrinted term
    | OHoles [HoleCtx]
    | OOK
    | OQuit
    | OSkip
