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

%%

Seq(X)
    : X Seq(X)                               { $1 : $2 }
    | X                                      { [$1] }

SemiEnd(X) : X ';'                           { $1 }

Decl :: { DeclT () }
Decl : name ':' Term '{' Seq(SemiEnd(Branch)) '}'
       { Val $1 $3 $5 }

Branch :: { BranchT () }
Branch
    : '(' name Seq(Id) ')' '=' Term          { Branch $2 $3 $6 }
    | name '=' Term                          { Branch $1 [] $3 }

Param :: { (IdT (), TermT ()) }
    : SingleTerm                             { (rawId "", $1) }
    | '(' Id ':' Term ')'                    { ($2, $4) }

Term :: { TermT () }
Term
    : '\\' Id ':' Term '->' Term             { Lambda $2 $4 $6 }
    | Seq(SingleTerm)                        { foldl1 App $1 }

SingleTerm :: { TermT () }
SingleTerm
    : Id                                     { Var $1 }
    | '(' Term ')'                           { $2 }

Id :: { IdT () }
Id : name                                    { rawId $1 }

{

happyError :: [Token] -> a
happyError _ = error "Parse error\n"

}
