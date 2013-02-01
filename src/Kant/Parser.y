{
{-# OPTIONS_GHC -w #-}

module Kant.Parser
    ( parseModule
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

lexer :: (Token -> Alex a) -> Alex a
lexer f = alexMonadScan' >>= f

-- TODO find a way to show the token
happyError :: Alex a
happyError =
    do (l, c) <- lineCol `liftM` alexGetInput
       fail ("Parse error at line " ++ show l ++ ", column " ++ show c)
  -- where
  --   showTok COLON    = "token `:'"
  --   showTok DATA     = "token `data'"
  --   showTok LBRACE   = "token `{'"
  --   showTok RBRACE   = "token `}'"
  --   showTok LPAREN   = "token `('"
  --   showTok RPAREN   = "token `)'"
  --   showTok LBRACK   = "token `['"
  --   showTok RBRACK   = "token `]'"
  --   showTok BAR      = "token `|'"
  --   showTok LAMBDA   = "token `\\'"
  --   showTok ARROW    = "token `->'"
  --   showTok DARROW   = "token `=>'"
  --   showTok CASE     = "token `case'"
  --   showTok (NAME n) = "identifier `" ++ n ++ "'"
  --   showTok (TYPE l) = "identifier `Type" ++ if l > 0 then show l else "" ++ "'"

parseModule :: String -> Either String Module
parseModule s = runAlex s parseModule_

parseDecl :: String -> Either String Decl
parseDecl s = runAlex s parseDecl_

parseTerm :: String -> Either String Term
parseTerm s = runAlex s parseTerm_

parseFile :: FilePath -> IO Module
parseFile fp = readFile fp >>= either fail return . parseModule

}
