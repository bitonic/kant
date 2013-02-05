{
{-# OPTIONS_GHC -w #-}

module Kant.Parser
    ( ParseResult
    , parseModule
    , parseFile
    , parseDecl
    , parseTerm
    ) where

import           Control.Monad (liftM)
import           Data.List (foldl1)

import           Kant.Lexer
import           Kant.Syntax

}

%name parseModule_
%name parseDecl_ Decl
%name parseTerm_ Term

%tokentype { Token }

%monad { Alex }
%lexer { lexer } { EOF }

%token
    ':'                 { COLON }
    '{'                 { LBRACE }
    '}'                 { RBRACE }
    '('                 { LPAREN }
    ')'                 { RPAREN }
    '['                 { LBRACK }
    ']'                 { RBRACK }
    '|'                 { BAR }
    '->'                { ARROW }
    '=>'                { DARROW }
    '\\'                { LAMBDA }
    ':='                { ASSIGN }
    'data'              { DATA }
    'case'              { CASE }
    'postulate'         { POSTULATE }
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
    :                                        { [] }
    | X                                      { [$1] }
    | X '|' Bar(X)                           { $1 : $3 }

Module :: { Module }
Module : Seq0(Decl)                          { Module $1 }

Decl :: { Decl }
Decl : Val                                   { ValDecl $1 }
     | 'postulate' name ':' SingleTerm       { Postulate $2 $4}
     | Data                                  { DataDecl $1 }

Data :: { Data }
Data : 'data' name Params ':' type '{' Bar(DataCon) '}'
       { Data $2 $3 $5 $7 }

Val :: { Val }
Val : name Params ':' Term ':=' SingleTerm   { valDecl $1 $2 $4 $6 }

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
    | 'case' Term '{' Bar(Branch) '}'        {% checkCase $2 $4 }
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

lexer :: (Token -> Alex a) -> Alex a
lexer f = alexMonadScan' >>= f

checkCase :: Term -> [(ConId, [Id], Term)] -> Alex Term
checkCase t₁ brs =
    case case_ t₁ brs of
        Left n   -> parseErr (":\nrepeated variable `" ++ n ++ "' in pattern")
        Right t₂ -> return t₂

parseErr :: String -> Alex a
parseErr err =
    do (l, c) <- lineCol `liftM` alexGetInput
       fail ("Parse error at line " ++ show l ++ ", column " ++ show c ++ err)

-- TODO find a way to find more info, e.g. tokens we were expecting or stuff
-- like this.
happyError :: Alex a
happyError = parseErr "."

-- | 'Left' for an error 'String', 'Right' for a result.
type ParseResult = Either String

parseModule :: String -> ParseResult Module
parseModule s = runAlex s parseModule_

parseDecl :: String -> ParseResult Decl
parseDecl s = runAlex s parseDecl_

parseTerm :: String -> ParseResult Term
parseTerm s = runAlex s parseTerm_

-- | Explodes if things go wrong.
parseFile :: FilePath -> IO Module
parseFile fp = readFile fp >>= either fail return . parseModule

}
