{
{-# OPTIONS_GHC -W #-}

module Kant.Parser (parseDecl, parseTerm) where

import Data.List (foldl1)

import Kant.Lexer
import Kant.Syntax

}

%name parseDecl
%name parseTerm Term
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
    type                { TYPE $$ }

%%

Seq(X)
    : X                                      { [$1] }
    | X Seq(X)                               { $1 : $2 }

Seq0(X)
    : {- empty -}                            { [] }
    | X Seq0(X)                              { $1 : $2 }

SemiEnd(X) : X ';'                           { $1 }

Decl :: { Decl }
Decl : name ':' Term '{' Seq0(SemiEnd(Branch)) '}'
       { Val $1 $3 $5 }
     | 'data' name Seq0(Param) ':' type '{' Seq0(SemiEnd(DataCon)) '}'
       { Data $2 (Params $3) $5 $7 }

Branch :: { Branch }
Branch
    : '(' name Seq(name) ')' '=' Term        { branch $2 $3 $6 }
    | name '=' Term                          { branch $1 [] $3 }

DataCon :: { (ConId, Params) }
DataCon : name Seq0(Param)                   { ($1, Params $2) }

Param :: { (Id, Term) }
    : SingleTerm                             { ("", $1) }
    | '(' name ':' Term ')'                  { ($2, $4) }

Term :: { Term }
Term
    : '\\' name ':' Term '->' Term           { lam $2 $4 $6 }
    | Seq(SingleTerm)                        { foldl1 App $1 }

SingleTerm :: { Term }
SingleTerm
    : name                                   { Var $1 }
    | type                                   { Type $1 }
    | '(' Term ')'                           { $2 }

{

happyError :: [Token] -> a
happyError _ = error "Parse error\n"

}
