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

import           Kant.Decl
import           Kant.Desugar
import           Kant.Lexer
import           Kant.Sugar
import           Kant.Term

}

%name parseModule_
%name parseDecl_ Decl
%name parseTerm_ Term

%tokentype { Token }

%monad { Alex }
%lexer { lexer } { EOF }

%token
    ':'                 { COLON }
    ','                 { COMMA }
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
    'record'            { RECORD }
    'postulate'         { POSTULATE }
    '*'                 { TYPE }
    '{!'                { LHOLE }
    '!}'                { RHOLE }
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

Comma(X)
    :                                        { [] }
    | X                                      { [$1] }
    | X ',' Comma(X)                         { $1 : $3 }

Module :: { SModuleSyn }
Module : Seq0(Decl)                          { SModule $1 }

Decl :: { SDeclSyn }
Decl : Val                                   { $1 }
     | 'postulate' name ':' SingleTerm       { SPostulate $2 $4}
     | Data                                  { $1 }
     | Record                                { $1 }

Data :: { SDeclSyn }
Data : 'data' name ':' Arr1(Type) '=>' '{' Bar(DataCon) '}'
       {% do pars <- tyConPars (fst $4); return (SData $2 pars $7) }

Record :: { SDeclSyn }
Record
     : 'record' name ':' Arr1(Type) '=>' name '{' Comma(RecProj) '}'
       {% do pars <- tyConPars (fst $4); return (SRecord $2 pars $6 $8) }

Val :: { SDeclSyn }
Val : name Seq0(Pi) ':' Term '=>' SingleTerm { SVal $1 (concat $2) $4 $6 }

DataCon :: { SConstr () }
DataCon : name ':' Term                      { ($1, $3) }

RecProj :: { (Id, STermSyn) }
RecProj : name ':' Term                      { ($1, $3) }



Term :: { STermSyn }
Term
    : '\\' Seq(Binder) '=>' Term             { SLam $2 $4 }
    | '\\' Seq0(LamParam) ':' Term '=>' Term { SAnn $2 $4 $6 }
    | Arr                                    { uncurry SArr $1 }

SingleTerm :: { STermSyn }
SingleTerm
    : name                                   { SV $1 }
    | Type                                   { $1 }
    | Hole                                   { $1 }
    | '(' Term ')'                           { $2 }

Type :: { STermSyn }
Type : '*'                                   { STy () }

Arr :: { ([SParam ()], STermSyn) }
Arr : Arr1(App)                              { $1 }

Arr1(X)
    : Seq(Pi) '->' Arr                       { first (concat $1 ++) $3 }
    | App '->' Arr                           { first ((Nothing, $1) :) $3 }
    | X                                      { ([], $1) }

Pi  :: { [SParam ()] }
Pi  : '[' Seq(Binder) ':' Term ']'           { zip $2 (repeat $4) }

App :: { STermSyn }
App : Seq(SingleTerm)                        { foldl1 SApp $1 }

Binder :: { Maybe Id }
Binder
    : '_'                                    { Nothing }
    | name                                   { Just $1 }

LamParam :: { SParam () }
LamParam
    : '[' Binder ':' Term ']'                { ($2, $4) }

Hole :: { STermSyn }
Hole : '{!' name Seq0(SingleTerm) '!}'       { SHole $2 $3 }

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

tyConPars :: [SParam ()] -> Alex [(Id, STermSyn)]
tyConPars pars = maybe happyError return
                       (sequence [do v <- mv; return (v, ty) | (mv, ty) <- pars])

type ParseError = String

-- | 'Left' for an error 'String', 'Right' for a result.
type ParseResult = Either ParseError

parseModule :: String -> ParseResult ModuleSyn
parseModule s = desugar <$> runAlex s parseModule_

parseDecl :: String -> ParseResult DeclSyn
parseDecl s = desugar <$> runAlex s parseDecl_

parseTerm :: String -> ParseResult TermSyn
parseTerm s = desugar <$> runAlex s parseTerm_

-- | Explodes if things go wrong.
parseFile :: FilePath -> IO ModuleSyn
parseFile fp = readFile fp >>= either fail return . parseModule

}
