{
{-# OPTIONS_GHC -W #-}

module Kant.Parser (parseKant) where

import Data.List (foldl1)

import Kant.Lexer
import Kant.Syntax

}

%name parseKant
%tokentype { Token }
%token
    ';'                 { SEMI }
    ':'                 { COLON }
    '{'                 { LBRACE }
    '}'                 { RBRACE }
    '('                 { LPAREN }
    ')'                 { RPAREN }
    '|'                 { BAR }
    '->'                { ARROW }
    '='                 { EQUALS }
    '\\'                { LAMBDA }
    'data'              { DATA }
    'of'                { OF }
    name                { NAME $$ }

%%

Term :: { Term }
Term : TermRaw                               { unRaw $1 }

TermRaw :: { TermRaw }
TermRaw
    : '\\' name ':' TermRaw '->' TermRaw     { Lambda (rawId $2) $4 $6 }
    | SingleTerms                            { foldl1 App $1 }

SingleTerms :: { [TermRaw] }
SingleTerms
    : SingleTerm                             { [$1] }
    | SingleTerm SingleTerms                 { $1 : $2 }

SingleTerm :: { TermRaw }
SingleTerm
    : name                                   { Var (rawId $1) }
    | '(' TermRaw ')'                        { $2 }

{

happyError :: [Token] -> a
happyError _ = error "Parse error\n"

}
