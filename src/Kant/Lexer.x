{
{-# OPTIONS_GHC -W #-}
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
    ";"                                   { \_ -> SEMI }
    ":"                                   { \_ -> COLON }
    "{"                                   { \_ -> LBRACE }
    "}"                                   { \_ -> RBRACE }
    "("                                   { \_ -> LPAREN }
    ")"                                   { \_ -> RPAREN }
    "|"                                   { \_ -> BAR }
    "->"                                  { \_ -> ARROW }
    "="                                   { \_ -> EQUALS }
    [\\]                                  { \_ -> LAMBDA }
    "data"                                { \_ -> DATA }
    "of"                                  { \_ -> OF }
    $alpha* ($alpha | $digit | $syms)     { NAME }

{
-- Each action has type :: String -> Token

data Token
    = COLON
    | SEMI
    | DATA
    | LBRACE
    | RBRACE
    | LPAREN
    | RPAREN
    | BAR
    | LAMBDA
    | ARROW
    | OF
    | EQUALS
    | NAME IdName
    deriving (Show, Eq, Ord)

lexKant :: String -> [Token]
lexKant = alexScanTokens
}
