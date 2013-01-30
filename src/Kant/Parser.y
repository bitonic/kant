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
    'case'              { CASE }
    'of'                { OF }
    'end'               { END }
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
Decl : name '=' Term ';'                     { Val $1 $3 }
     | 'data' name Seq0(Param) ':' type Seq0(DataCon) 'end'
       { Data $2 (Params $3) $5 $6 }

Param :: { (Id, Term) }
    : SingleTerm                             { ("", $1) }
    | '(' name ':' Term ')'                  { ($2, $4) }

DataCon :: { Constr }
DataCon : '|' name Seq0(Param)               { ($2, Params $3) }

Term :: { Term }
Term
    : '\\' name ':' Term '->' Term           { lam $2 $4 $6 }
    | 'case' Term Seq0(Branch) 'end'         { case_ $2 $3 }
    | Seq(SingleTerm)                        { foldl1 App $1 }

Branch :: { (ConId, [Id], Term) }
Branch : '|' name Seq0(name) '->' Term       { ($2, $3, $5) }

SingleTerm :: { Term }
SingleTerm
    : name                                   { Var $1 }
    | type                                   { Type $1 }
    | '(' Term ')'                           { $2 }

{

happyError :: [Token] -> a
happyError _ = error "Parse error\n"

}
