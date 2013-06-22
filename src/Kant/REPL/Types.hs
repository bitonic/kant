module Kant.REPL.Types
    ( Output(..)
    ) where

import           Kant.Term
import           Kant.Env

data Output
    = OTyCheck TmRefId [HoleCtx] -- Type checked term, with holes
    | OPretty TmRefId            -- Term to pretty print
    | OInfo Free                 -- Info about an identifier
    | OHoles [HoleCtx]           -- Just holes, classically after loading a file
    | OOK                        -- Something succeeded
    | OQuit                      -- Print goodbye message and quit
    | OHelp                      -- Print help message
    | OSkip                      -- Do nothing
