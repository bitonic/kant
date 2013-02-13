module Kant.REPL.Types
    ( Output(..)
    , REPLError(..)
    ) where

import qualified Text.Parsec as Parsec
import           Control.Monad.Error (Error(..))

import           Kant.Term
import           Kant.Parser
import           Kant.TyCheck

data Output
    = OTyCheck Term             -- Type of term
    | OEval Term                -- Normal form of term
    | OOK
    | OQuit
    | OSkip

data REPLError
    = CmdParse Parsec.ParseError
    | TermParse ParseError
    | TyCheck TyCheckError
    | IOError IOError

instance Error REPLError where
    strMsg = undefined          -- I don't care, I want the 'Error' instance
