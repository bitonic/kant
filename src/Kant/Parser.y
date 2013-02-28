{
{-# OPTIONS_GHC -w #-}

module Kant.Parser
    ( ParseError
    , ParseResult
    , parseModule
    , parseFile
    , parseDecl
    , parseTerm
    ) where

import           Control.Applicative ((<$>))
import           Control.Arrow (first)
import           Control.Monad (liftM)
import           Data.List (foldl1)

import           Kant.Term
import           Kant.Lexer
import           Kant.Sugar
import           Kant.Desugar

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
    '_'                 { UNDERSCORE }
    'data'              { DATA }
    'postulate'         { POSTULATE }
    'Type'              { TYPE }
    name                { NAME $$ }

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

Module :: { SModule }
Module : Seq0(Decl)                          { SModule $1 }

Decl :: { SDecl }
Decl : Val                                   { $1 }
     | 'postulate' name ':' SingleTerm       { SPostulate $2 $4}
     | Data                                  { $1 }

Data :: { SDecl }
Data : 'data' name Params '{' Bar(DataCon) '}'
       { SData $2 $3 $5 }

Val :: { SDecl }
Val : name Params '=>' SingleTerm { SVal $1 $2 $4 }

Params :: { [SParam] }
Params : Seq0(Param)                         { $1 }

Param :: { SParam }
Param
    : '[' Seq(name) ':' Term ']'             { (Just $2, $4) }
    | SingleTerm                             { (Nothing, $1) }

DataCon :: { SConstr }
DataCon : name Params                        { ($1, $2) }

Term :: { STerm }
Term
    : '\\' Seq(Param) '=>' Term              { SLam $2 $4 }
    | Arr                                    { uncurry SArr $1 }

SingleTerm :: { STerm }
SingleTerm
    : name                                   { SV $1 }
    | 'Type'                                 { STy }
    | '(' Term ')'                           { $2 }

Arr :: { ([SParam], STerm) }
Arr : App '->' Arr                           { first ((Nothing, $1):) $3 }
    | '[' Seq(name) ':' Term ']' '->' Arr    { first ((Just $2, $4):) $7 }
    | App                                    { ([], $1) }

App :: { STerm }
App : Seq(SingleTerm)                        { foldl1 SApp $1 }

{

lexer :: (Token -> Alex a) -> Alex a
lexer f = alexMonadScan' >>= f

parseErr :: String -> Alex a
parseErr err =
    do (l, c) <- lineCol `liftM` alexGetInput
       alexError ("Parse error at line " ++ show l ++ ", column " ++ show c ++ err)

-- TODO find a way to find more info, e.g. tokens we were expecting or stuff
-- like this.
happyError :: Alex a
happyError = parseErr "."

type ParseError = String

-- | 'Left' for an error 'String', 'Right' for a result.
type ParseResult = Either ParseError

parseModule :: String -> ParseResult SModule
parseModule s = runAlex s parseModule_

parseDecl :: String -> ParseResult SDecl
parseDecl s = runAlex s parseDecl_

parseTerm :: String -> ParseResult TermId
parseTerm s = desugarT <$> runAlex s parseTerm_

-- | Explodes if things go wrong.
parseFile :: FilePath -> IO SModule
parseFile fp = readFile fp >>= either fail return . parseModule

}
