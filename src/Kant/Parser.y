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

import           Control.Monad (liftM)
import           Data.List (foldl1)

import           Kant.Lexer
import           Kant.Sugar

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
    'postulate'         { POSTULATE }
    'return'            { RETURN }
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

Module :: { SModule }
Module : Seq0(Decl)                          { SModule $1 }

Decl :: { SDecl }
Decl : Val                                   { $1 }
     | 'postulate' name ':' SingleTerm       { SPostulate $2 $4}
     | Data                                  { $1 }

Data :: { SDecl }
Data : 'data' name Params ':' type '{' Bar(DataCon) '}'
       { SData $2 $3 $5 $7 }

Val :: { SDecl }
Val : name Params ':' Term '=>' SingleTerm   { SVal $1 $2 $4 $6 }

Params :: { [SParam] }
Params : Seq0(Param)                         { concat $1 }

Param :: { [SParam] }
Param
    : '[' Seq(name) ':' Term ']'             { zip (map Just $2) (repeat $4) }
    | SingleTerm                             { [(Nothing, $1)] }

DataCon :: { SConstr }
DataCon : name Params                        { ($1, $2) }

Term :: { STerm }
Term
    : '\\' Seq(Param) '=>' Term              { SLam (concat $2) $4 }
    | 'case' name 'return' Term '{' Bar(Branch) '}'
      { SCase $2 $4 $6 }
    | Arr                                    { $1 }

Branch :: { SBranch }
Branch : name Seq0(name) '=>' Term           { ($1, $2, $4) }

SingleTerm :: { STerm }
SingleTerm
    : name                                   { SVar $1 }
    | type                                   { SType $1 }
    | '(' Term ')'                           { $2 }

Arr :: { STerm }
Arr : App '->' Arr                           { SArr Nothing $1 $3 }
    | '(' name ':' Term ')' '->' Arr         { SArr (Just $2) $4 $7 }
    | App                                    { $1 }

App :: { STerm }
App : Seq(SingleTerm)                        { foldl1 SApp $1 }

{

lexer :: (Token -> Alex a) -> Alex a
lexer f = alexMonadScan' >>= f

-- TODO move this in the desugaring place
-- checkCase :: Id -> Term -> [(ConId, [Id], Term)] -> Alex Term
-- checkCase n ty brs =
--     case case_ n ty brs of
--         Left n  -> parseErr (":\nrepeated variable `" ++ n ++ "' in pattern")
--         Right t -> return t

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

parseTerm :: String -> ParseResult STerm
parseTerm s = runAlex s parseTerm_

-- | Explodes if things go wrong.
parseFile :: FilePath -> IO SModule
parseFile fp = readFile fp >>= either fail return . parseModule

}
