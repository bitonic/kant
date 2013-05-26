module Kant.Error (KError(..)) where

import           Control.Monad.Error (Error)
import qualified Text.Parsec as Parsec

import           Kant.Parser
import           Kant.Term

data KError
    = OutOfBounds Id
    | DuplicateName Id
    | Mismatch TmRefId TmRefId TmRefId
      -- TODO this could be made better.
      -- ^ The 'Maybe' is there because sometimes we need to invoke this error
      -- while working with primitive types and we don't really have anything to
      -- show.
    | ExpectingFunction (Maybe TmRefId) TmRefId
    | ExpectingType TmRefId TmRefId
    | ExpectingTypeCon ConId TmRefId
    | ExpectingTypeData ConId ConId TmRefId
    | WrongRecTypePos ConId ConId TmRefId
    | UntypedTm TmRefId
    | UnexpectedHole HoleId
    | NotEnoughArguments ConId
    | CyclicTypes               -- TODO more descriptive
      -- REPL errors
    | CmdParse Parsec.ParseError
    | TmParse ParseError
    | IOError IOError
    deriving (Show)

instance Error KError where
