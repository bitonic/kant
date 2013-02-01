{
{-# OPTIONS_GHC -w #-}

module Kant.Parser
    ( parseModule
    , parseFile
    , parseDecl
    , parseTerm
    ) where

import           Control.Applicative ((<$>))
import           Data.List (foldl1)

import           Kant.Lexer
import           Kant.Syntax

}

%name parseModule_
%name parseDecl_ Decl
%name parseTerm_ Term

%tokentype { (Token, Position) }

%monad { ParseM }

%token
    ':'                 { (COLON, _) }
    '{'                 { (LBRACE, _) }
    '}'                 { (RBRACE, _) }
    '('                 { (LPAREN, _) }
    ')'                 { (RPAREN, _) }
    '['                 { (LBRACK, _) }
    ']'                 { (RBRACK, _) }
    '|'                 { (BAR, _) }
    '->'                { (ARROW, _) }
    '=>'                { (DARROW, _) }
    '\\'                { (LAMBDA, _) }
    'data'              { (DATA, _) }
    'case'              { (CASE, _) }
    name                { (NAME $$, _) }
    type                { (TYPE $$, _) }

%%

Seq(X)
    : X                                      { [$1] }
    | X Seq(X)                               { $1 : $2 }

Seq0(X)
    : {- empty -}                            { [] }
    | X Seq0(X)                              { $1 : $2 }

Bar(X)
    :                                        { [] }
    | X                                      { [$1] }
    | X '|' Bar(X)                           { $1 : $3 }

Module :: { Module }
Module : Seq0(Decl)                          { Module $1 }

Decl :: { Decl }
Decl : name '{' Term '}'                     { Val $1 $3 }
     | 'data' name Params ':' type '{' Bar(DataCon) '}'
       { DataDecl (Data $2 $3 $5 $7) }

Params :: { [Param] }
Params : Seq0(Param)                         { concat $1 }

Param :: { [Param] }
Param
    : '[' Seq(name) ':' Term ']'             { zip $2 (repeat $4) }
    | SingleTerm                             { [(discarded, $1)] }

DataCon :: { Constr }
DataCon : name Params                        { ($1, $2) }

Term :: { Term }
Term
    : '\\' Seq(Param) '=>' Term              { lams (concat $2) $4 }
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

App :: { Term }
App : Seq(SingleTerm)                        { foldl1 App $1 }

{

type ParseError = String
type ParseM = Either ParseError

happyError :: [(Token, Position)] -> ParseM a
happyError [] = fail "Parse error"
happyError ((tok, Position l c) : _) =
    fail ("Parse error at " ++ showTok tok ++ ", line " ++ show l ++
          ", column " ++ show c)
  where
    showTok COLON    = "token `:'"
    showTok DATA     = "token `data'"
    showTok LBRACE   = "token `{'"
    showTok RBRACE   = "token `}'"
    showTok LPAREN   = "token `('"
    showTok RPAREN   = "token `)'"
    showTok LBRACK   = "token `['"
    showTok RBRACK   = "token `]'"
    showTok BAR      = "token `|'"
    showTok LAMBDA   = "token `\\'"
    showTok ARROW    = "token `->'"
    showTok DARROW   = "token `=>'"
    showTok CASE     = "token `case'"
    showTok (NAME n) = "identifier `" ++ n ++ "'"
    showTok (TYPE l) = "identifier `Type" ++ if l > 0 then show l else "" ++ "'"

parseModule :: String -> ParseM Module
parseModule = parseModule_ . lexToks

parseDecl :: String -> ParseM Decl
parseDecl = parseDecl_ . lexToks

parseTerm :: String -> ParseM Term
parseTerm = parseTerm_ . lexToks

parseFile :: FilePath -> IO Module
parseFile fp = readFile fp >>= either fail return . parseModule

}
