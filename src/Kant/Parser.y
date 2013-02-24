{
{-# OPTIONS_GHC -w #-}

module Kant.Parser
    ( ParseError
    , ParseResult
    , parseModule
    , parseModule'
    , parseFile
    , parseFile'
    , parseDecl
    , parseDecl'
    , parseTerm
    , parseTerm'
    ) where

import           Control.Applicative ((<$>))
import           Control.Arrow (first)
import           Control.Monad (liftM)
import           Data.List (foldl1)

import           Control.Monad.Identity (runIdentity)

import           Kant.Term
import           Kant.Lexer
import           Kant.Sugar
import           Kant.Environment
import           Kant.Uniquify

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
    'case'              { CASE }
    'postulate'         { POSTULATE }
    'return'            { RETURN }
    'as'                { AS }
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
Val : name ValParams ':' Term '=>' SingleTerm { SVal $1 $2 $4 $6 }

ValParams :: { SValParams }
ValParams
    : Params ValParams1                      { SValParams $1 $2 }

ValParams1 :: { Maybe [SParam] }
ValParams1
    : '|' Params                             { Just $2 }
    |  {- empty -}                           { Nothing }

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
    | 'case' name 'return' Term '{' Bar(Branch) '}'
      {% checkCase (SVar $2) (Just $2) $4 $6 }
    | 'case' Term 'as' name 'return' Term '{' Bar(Branch) '}'
      {% checkCase $2 (Just $4) $6 $8 }
    | Arr                                    { uncurry SArr $1 }

Branch :: { SBranch }
Branch : name Seq0(Binder) '=>' Term         { ($1, $2, $4) }

SingleTerm :: { STerm }
SingleTerm
    : name                                   { SVar $1 }
    | type                                   { SType $1 }
    | '(' Term ')'                           { $2 }

Arr :: { ([SParam], STerm) }
Arr : App '->' Arr                           { first ((Nothing, $1):) $3 }
    | '[' Seq(name) ':' Term ']' '->' Arr    { first ((Just $2, $4):) $7 }
    | App                                    { ([], $1) }

App :: { STerm }
App : Seq(SingleTerm)                        { foldl1 SApp $1 }

Binder :: { Maybe Id }
Binder
    : name                                   { Just $1 }
    | '_'                                    { Nothing }

{

lexer :: (Token -> Alex a) -> Alex a
lexer f = alexMonadScan' >>= f

checkCase :: STerm -> Maybe Id -> STerm -> [SBranch] -> Alex STerm
checkCase t n ty brs =
    case scase t n ty brs of
        Left n  -> parseErr (":\nrepeated variable `" ++ n ++ "' in pattern")
        Right t -> return t

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

parseModule :: String -> ParseResult ModuleV
parseModule s = desugar <$> runAlex s parseModule_

parseEnvM p = either (return . Left) (\m -> Right `liftM` uniquify m) . p

parseModule' :: MonadEnv m => String -> m (ParseResult Module)
parseModule' = parseEnvM parseModule

parseDecl :: String -> ParseResult DeclV
parseDecl s = desugar <$> runAlex s parseDecl_

parseDecl' :: MonadEnv m => String -> m (ParseResult Decl)
parseDecl' = parseEnvM parseDecl

parseTerm :: String -> ParseResult TermV
parseTerm s = desugar <$> runAlex s parseTerm_

parseTerm' :: MonadEnv m => String -> m (ParseResult Term)
parseTerm' = parseEnvM parseTerm

-- | Explodes if things go wrong.
parseFile :: FilePath -> IO ModuleV
parseFile fp = readFile fp >>= either fail return . parseModule

parseFile' :: Env -> FilePath -> IO (Module, Env)
parseFile' env fp = runIdentity . runEnv env . uniquify <$> parseFile fp

}
