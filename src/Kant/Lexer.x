{
{-# OPTIONS_GHC -w #-}
module Kant.Lexer
    ( Alex(..)
    , alexMonadScan'
    , alexGetInput
    , lineCol
    , Token(..)
    , runAlex
    , alexError
    ) where

import           Kant.Common
import           Kant.Sugar
import           Kant.Term

}

%wrapper "monad"

$digit = [0-9]
$alpha = [a-zA-Z]
$syms  = ['_\-]

tokens :-
    $white+                               ;
    "--".*                                ;
    ":"                                   { simpleTok COLON }
    ","                                   { simpleTok COMMA }
    "{"                                   { simpleTok LBRACE }
    "}"                                   { simpleTok RBRACE }
    "("                                   { simpleTok LPAREN }
    ")"                                   { simpleTok RPAREN }
    "["                                   { simpleTok LBRACK }
    "]"                                   { simpleTok RBRACK }
    "|"                                   { simpleTok BAR }
    "->"                                  { simpleTok ARROW }
    "=>"                                  { simpleTok DARROW }
    "_"                                   { simpleTok UNDERSCORE }
    [\\]                                  { simpleTok LAMBDA }
    "data"                                { simpleTok DATA }
    "record"                              { simpleTok RECORD }
    "postulate"                           { simpleTok POSTULATE }
    "*"                                   { simpleTok TYPE }
    "{!"                                  { simpleTok LHOLE }
    "!}"                                  { simpleTok RHOLE }
    $alpha ($alpha | $digit | $syms)*     { stringTok NAME }

{

data Token
    = COLON
    | DATA
    | LBRACE
    | RBRACE
    | LPAREN
    | RPAREN
    | LBRACK
    | RBRACK
    | BAR
    | LAMBDA
    | ARROW
    | DARROW
    | POSTULATE
    | NAME Id
    | TYPE
    | EOF
    | UNDERSCORE
    | LHOLE
    | RHOLE
    | COMMA
    | RECORD
    deriving (Show, Eq, Ord)

type Action r = (AlexPosn, Char, [Byte], String) -> Int -> Alex r

simpleTok :: Token -> Action Token
simpleTok tok _ _ = return tok

getS :: (AlexPosn, Char, [Byte], String) -> Int -> String
getS (_, _, _, input) len = take len input

stringTok :: (String -> Token) -> Action Token
stringTok f inp len = return (f (getS inp len))

alexEOF :: Alex Token
alexEOF = return EOF

lineCol :: AlexInput -> (Int, Int)
lineCol (AlexPn _ l c, _, _, _) = (l, c)

alexMonadScan' :: Alex Token
alexMonadScan' = do
    inp <- alexGetInput
    sc <- alexGetStartCode
    case alexScan inp sc of
        AlexEOF -> alexEOF
        AlexError inp' ->
            let (l, c) = lineCol inp' in
            alexError ("Lexical error at line " ++ show l ++ ", column " ++ show c)
        AlexSkip  inp' len ->
            alexSetInput inp' >> alexMonadScan'
        AlexToken inp' len action ->
            alexSetInput inp' >> action (ignorePendingBytes inp) len

trimHole :: String -> String
trimHole = trim . tail . tail . init . init

}
