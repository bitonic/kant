{
{-# OPTIONS_GHC -w #-}
module Kant.Lexer
    ( lexToks
    , Token(..)
    , Position(..)
    ) where

import Kant.Syntax
}

%wrapper "posn"

$digit = 0-9
$alpha = [a-zA-Z]
$syms  = ['_]

tokens :-
    $white+                               ;
    "--".*                                ;
    ":"                                   { simpleTok COLON }
    ";"                                   { simpleTok SEMI }
    "{"                                   { simpleTok LBRACE }
    "}"                                   { simpleTok RBRACE }
    "("                                   { simpleTok LPAREN }
    ")"                                   { simpleTok RPAREN }
    "["                                   { simpleTok LBRACK }
    "]"                                   { simpleTok RBRACK }
    "|"                                   { simpleTok BAR }
    "->"                                  { simpleTok ARROW }
    "=>"                                  { simpleTok DARROW }
    "="                                   { simpleTok EQUALS }
    [\\]                                  { simpleTok LAMBDA }
    "data"                                { simpleTok DATA }
    "case"                                { simpleTok CASE }
    "Type" $digit*                        { typeTok }
    $alpha* ($alpha | $digit | $syms)     { stringTok NAME }

{
-- Each action has type :: String -> Token

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
    | SEMI
    | LAMBDA
    | ARROW
    | DARROW
    | CASE
    | EQUALS
    | NAME Id
    | TYPE Int
    deriving (Show, Eq, Ord)

data Position = Position { lineNum :: !Int
                         , colNum  :: !Int
                         }
    deriving (Show, Eq)

toPosition :: AlexPosn -> Position
toPosition (AlexPn _ l c) = Position l c

simpleTok :: Token -> AlexPosn -> String -> (Token, Position)
simpleTok tok pos _ = (tok, toPosition pos)

stringTok :: (String -> Token) -> AlexPosn -> String -> (Token, Position)
stringTok f pos s = (f s, toPosition pos)

lexToks :: String -> [(Token, Position)]
lexToks = alexScanTokens

typeTok :: AlexPosn -> String -> (Token, Position)
typeTok pos s = (TYPE (if length s > len then read (drop len s) else 0),
                 toPosition pos)
  where len = length "Type"

}
