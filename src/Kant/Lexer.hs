module Kant.Lexer
    ( Parser
    , ParseError
    , ParseResult
    , runParser
    , Token(..)
    , lexToken
    ) where

import           Control.Applicative ((*>), (<*), (<$), (<$>), (<*>))
import           Control.Monad (msum)

import           Text.Parsec hiding (runParser, ParseError)
import           Text.Parsec.String

import           Kant.Term

type ParseError  = String
type ParseResult = Either ParseError

runParser :: String -> Parser a -> ParseResult a
runParser s p =
    case parse (spaces *> p) "" s of
        Left err -> let pos = errorPos err
                    in Left ("Parse error at line " ++ show (sourceLine pos) ++
                             ", " ++ "column " ++ show (sourceColumn pos))
        Right x  -> Right x

data Token
    = COLON
    | DATA
    | LBRACE
    | RBRACE
    | LPAREN
    | RPAREN
    | LBRACK
    | RBRACK
    | BAR
    | LAMBDA
    | ARROW
    | DARROW
    | POSTULATE
    | NAME Id
    | TYPE
    | EOF
    | UNDERSCORE
    | LHOLE
    | RHOLE
    | COMMA
    | RECORD
    deriving (Show, Eq, Ord)

lexeme :: Parser a -> Parser a
lexeme p = try p <* spaces

lexToken :: Parser Token
lexToken = tok
  where
    simpleTok s x = lexeme (x <$ string s)
    simpleToks =
        [(":",  COLON),  (",",  COMMA),  ("{",  LBRACE), ("}",  RBRACE),
         ("(",  LPAREN), (")",  RPAREN), ("[",  LBRACK), ("]",  RBRACK),
         ("|",  BAR),    ("->", ARROW),  ("=>", DARROW), ("_",  UNDERSCORE),
         ("\\", LAMBDA), ("*",  TYPE),   ("{!", LHOLE),  ("!}", RHOLE),
         ("data", DATA), ("record", RECORD), ("postulate", POSTULATE)
        ]

    ident = (:) <$> alphaNum <*> many (alphaNum <|> digit <|> oneOf "'_-")

    tok =
        msum [ lexeme (string "--" *> manyTill anyChar (char '\n')) *> tok
             , msum [simpleTok s t | (s, t) <- simpleToks]
             , lexeme (NAME <$> ident)
             , EOF <$ eof
             ]
