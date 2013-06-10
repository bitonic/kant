module Kant.Lexer
    ( Parser
    , ParseError
    , ParseResult
    , runParser
    , Token(..)
    , lexToken
    ) where

import           Control.Applicative ((*>), (<*), (<$), (<$>), (<*>))
import           Control.Monad (msum, void)

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
    | UNDER
    | LHOLE
    | RHOLE
    | COMMA
    | RECORD
    | EQUAL
    | COE
    | COH
    | FORALL
    | TOP
    | BOT
    | AND
    | PROP
    | LDEC
    | RDEC
    deriving (Show, Eq, Ord)

lexeme :: Parser a -> Parser a
lexeme p = try p <* spaces

lexToken :: Parser Token
lexToken = tok
  where
    simpleTok s x = lexeme (x <$ string s)
    simpleToks =
        [ (":",         COLON    )
        , (",",         COMMA    )
        , ("{",         LBRACE   )
        , ("}",         RBRACE   )
        , ("(",         LPAREN   )
        , (")",         RPAREN   )
        , ("[",         LBRACK   )
        , ("]",         RBRACK   )
        , ("|",         BAR      )
        , ("->",        ARROW    )
        , ("→",         ARROW    )
        , ("=>",        DARROW   )
        , ("⇒",         DARROW   )
        , ("/\\",       AND      )
        , ("∧",         AND      )
        , ("forall",    FORALL   )
        , ("∀",         FORALL   )
        , ("Top",       TOP      )
        , ("⊤",         TOP      )
        , ("Bot",       BOT      )
        , ("⊥",         BOT      )
        , ("_",         UNDER    )
        , ("\\",        LAMBDA   )
        , ("λ",         LAMBDA   )
        , ("*",         TYPE     )
        , ("⋆",         TYPE     )
        , ("{|",        LHOLE    )
        , ("|}",        RHOLE    )
        , ("=",         EQUAL    )
        , ("[|",        LDEC     )
        , ("⟦",         LDEC     )
        , ("|]",        RDEC     )
        , ("⟧",         RDEC     )
        , ("Prop",      PROP     )
        , ("data",      DATA     )
        , ("record",    RECORD   )
        , ("postulate", POSTULATE)
        , ("coe",       COE      )
        , ("coh",       COH      )
        ]

    ident = (:) <$> alphaNum <*> many (alphaNum <|> digit <|> oneOf "'_-")

    tok =
        msum [ lexeme (string "--" *> manyTill anyChar (void (char '\n') <|> eof))
               *> tok
             , msum [simpleTok s t | (s, t) <- simpleToks]
             , lexeme (NAME <$> ident)
             , EOF <$ eof
             ]
