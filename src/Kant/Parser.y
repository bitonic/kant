{
{-# OPTIONS_GHC -w #-}

module Kant.Parser (parseDecl, parseTerm) where

import           Data.List (foldl1)

import           Kant.Lexer
import           Kant.Syntax

}

%name parseDecl_
%name parseTerm_ Term
%tokentype { Token }
%token
    ':'                 { COLON }
    '{'                 { LBRACE }
    '}'                 { RBRACE }
    '('                 { LPAREN }
    ')'                 { RPAREN }
    '|'                 { BAR }
    '->'                { ARROW }
    '=>'                { DARROW }
    '='                 { EQUALS }
    '\\'                { LAMBDA }
    'data'              { DATA }
    'case'              { CASE }
    name                { NAME $$ }
    type                { TYPE $$ }

%%

Seq(X)
    : X                                      { [$1] }
    | X Seq(X)                               { $1 : $2 }

Seq0(X)
    : {- empty -}                            { [] }
    | X Seq0(X)                              { $1 : $2 }

Bar(X)
    : X                                      { [$1] }
    | X '|' Bar(X)                           { $1 : $3 }

Decl :: { Decl }
Decl : name '=' Term                         { Val $1 $3 }
     | 'data' name Seq0(Param) ':' type '{' Bar(DataCon) '}'
       { DataDecl (Data $2 $3 $5 $7) }

Param :: { (Id, Term) }
    : SingleTerm                             { ("", $1) }
    | '(' name ':' Term ')'                  { ($2, $4) }

DataCon :: { Constr }
DataCon : name Seq0(Param)                   { ($1, $2) }

Term :: { Term }
Term
    : '\\' name ':' Term '=>' Term           { lam $2 $4 $6 }
    | 'case' Term '{' Bar(Branch) '}'        { case_ $2 $4 }
    | Arr                                    { $1 }

Branch :: { (ConId, [Id], Term) }
Branch : name Seq0(name) '=>' Term           { ($1, $2, $4) }

SingleTerm :: { Term }
SingleTerm
    : name                                   { Var $1 }
    | type                                   { Type $1 }
    | '(' Term ')'                           { $2 }

Arr :: { Term }
Arr : App '->' Arr                           { arr $1 $3 }
    | '(' name ':' Term ')' '->' Arr         { pi_ $2 $4 $7 }
    | App                                    { $1 }

App :: { Term}
App : Seq(SingleTerm)                        { foldl1 App $1 }


{

happyError :: [Token] -> a
happyError _ = error "Parse error\n"

parseDecl :: String -> Decl
parseDecl = parseDecl_ . lexKant

parseTerm :: String -> Term
parseTerm = parseTerm_ . lexKant

}
