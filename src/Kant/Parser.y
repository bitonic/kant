{
{-# OPTIONS_GHC -w #-}

module Kant.Parser
    ( ParseError
    , ParseResult
    , parseModule
    , parseFile
    , parseDecl
    , parseTm
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

import Debug.Trace

}

%name parseModule_
%name parseDecl_ Decl
%name parseTm_ Tm

%tokentype { Token }

%monad { Parser }
%lexer { lexer } { EOF }

%token
    ':'                 { COLON     }
    ','                 { COMMA     }
    '{'                 { LBRACE    }
    '}'                 { RBRACE    }
    '('                 { LPAREN    }
    ')'                 { RPAREN    }
    '['                 { LBRACK    }
    ']'                 { RBRACK    }
    '|'                 { BAR       }
    '->'                { ARROW     }
    '=>'                { DARROW    }
    '\\'                { LAMBDA    }
    '_'                 { UNDER     }
    '='                 { EQUAL     }
    'data'              { DATA      }
    'record'            { RECORD    }
    'postulate'         { POSTULATE }
    '*'                 { TYPE      }
    '{!'                { LHOLE     }
    '!}'                { RHOLE     }
    name                { NAME $$   }

%nonassoc '='
%right '->'

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
     | 'postulate' name ':' SingleTm         { SPostulate $2 $4}
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
Val : name Seq0(Pi) ':' Tm '=>' SingleTm     { SVal $1 (concat $2) $4 $6 }

DataCon :: { SConstr () }
DataCon : name ':' Tm                        { ($1, $3) }

RecProj :: { (Id, STmSyn) }
RecProj : name ':' Tm                        { ($1, $3) }

Tm :: { STmSyn }
Tm
    : '\\' Seq(Binder) '=>' Tm               { SLam $2 $4 }
    | '\\' Seq0(LamParam) ':' Tm '=>' Tm     { SAnn $2 $4 $6 }
    | Arr                                    { uncurry SArr $1 }

SingleTm :: { STmSyn }
SingleTm
    : name                                   { SV $1 }
    | Type                                   { $1 }
    | Hole                                   { $1 }
    | TyEq                                   { $1 }
    | HeEq                                   { $1 }
    | '(' Tm ')'                             { $2 }

Type :: { STmSyn }
Type : '*'                                   { STy () }

Arr :: { ([SParam ()], STmSyn) }
Arr : Arr1(App)                              { $1 }

Arr1(X)
    : Seq(Pi) '->' Arr                       { first (concat $1 ++) $3 }
    | App '->' Arr                           { first ((Nothing, $1) :) $3 }
    | X                                      { ([], $1) }

Pi  :: { [SParam ()] }
Pi  : '[' Seq(Binder) ':' Tm ']'             { zip $2 (repeat $4) }

App :: { STmSyn }
App : Seq(SingleTm)                          { foldl1 SApp $1 }

Binder :: { Maybe Id }
Binder
    : '_'                                    { Nothing }
    | name                                   { Just $1 }

LamParam :: { SParam () }
LamParam
    : '[' Binder ':' Tm ']'                  { ($2, $4) }

Hole :: { STmSyn }
Hole : '{!' name Seq0(SingleTm) '!}'         { SHole $2 $3 }

TyEq :: { STmSyn }
TyEq : SingleTm '=' SingleTm                 { STyEq $1 $3 }

HeEq :: { STmSyn }
HeEq : '(' SingleTm ':' SingleTm ')' '=' '(' SingleTm ':' SingleTm ')'
       { SHeEq $2 $4 $8 $10 }

{

lexer :: (Token -> Parser a) -> Parser a
lexer = (lexToken >>=)

-- TODO find a way to find more info, e.g. tokens we were expecting or stuff
-- like this.
happyError :: Parser a
happyError = fail "Parse error"

tyConPars :: [SParam ()] -> Parser [(Id, STmSyn)]
tyConPars pars =
    maybe happyError return
          (sequence [do v <- mv; return (v, ty) | (mv, ty) <- pars])

parseModule :: String -> ParseResult ModuleSyn
parseModule s = desugar <$> runParser s parseModule_

parseDecl :: String -> ParseResult DeclSyn
parseDecl s = desugar <$> runParser s parseDecl_

parseTm :: String -> ParseResult TmSyn
parseTm s = desugar <$> runParser s parseTm_

-- | Explodes if things go wrong.
parseFile :: FilePath -> IO ModuleSyn
parseFile fp = readFile fp >>= either (fail . show) return . parseModule

}

