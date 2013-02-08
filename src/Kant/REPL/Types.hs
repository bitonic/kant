module Kant.REPL.Types
    ( Output(..)
    , Error(..)
    ) where

import qualified Text.Parsec as Parsec

import           Kant.Syntax
import           Kant.Parser
import           Kant.TyCheck

data Output
    = OTyCheck Term             -- Type of term
    | OEval Term                -- Normal form of term
    | ODecl
    | OQuit
    | OSkip

data Error
    = CmdParse Parsec.ParseError
    | TermParse ParseError
    | TyCheck TyCheckError
