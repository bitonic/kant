{
{-# OPTIONS_GHC -w #-}
module Kant.Lexer (lexKant, Token(..)) where

import Kant.Syntax
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$syms  = ['_]

tokens :-
    $white+                               ;
    "--".*                                ;
    ":"                                   { \_ -> COLON }
    "{"                                   { \_ -> LBRACE }
    "}"                                   { \_ -> RBRACE }
    "("                                   { \_ -> LPAREN }
    ")"                                   { \_ -> RPAREN }
    "|"                                   { \_ -> BAR }
    "->"                                  { \_ -> ARROW }
    "=>"                                  { \_ -> DARROW }
    "="                                   { \_ -> EQUALS }
    [\\]                                  { \_ -> LAMBDA }
    "data"                                { \_ -> DATA }
    "case"                                { \_ -> CASE }
    "Type" $digit*                        { getLevel }
    $alpha* ($alpha | $digit | $syms)     { NAME }

{
-- Each action has type :: String -> Token

data Token
    = COLON
    | DATA
    | LBRACE
    | RBRACE
    | LPAREN
    | RPAREN
    | BAR
    | LAMBDA
    | ARROW
    | DARROW
    | CASE
    | EQUALS
    | NAME Id
    | TYPE Int
    deriving (Show, Eq, Ord)

lexKant :: String -> [Token]
lexKant = alexScanTokens

getLevel :: String -> Token
getLevel s = TYPE (if length s > len then read (drop len s) else 0)
  where len = length "Type"
}
