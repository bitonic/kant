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

import           Kant.Sugar

}

%wrapper "monad"

$digit = [0-9]
$alpha = [a-zA-Z]
$syms  = ['_]

tokens :-
    $white+                               ;
    "--".*                                ;
    ":"                                   { simpleTok COLON }
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
    "case"                                { simpleTok CASE }
    "postulate"                           { simpleTok POSTULATE }
    "return"                              { simpleTok RETURN }
    "as"                                  { simpleTok AS }
    "Type" $digit*                        { typeTok }
    $alpha* ($alpha | $digit | $syms)     { stringTok NAME }

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
    | CASE
    | POSTULATE
    | NAME Id
    | TYPE Level
    | EOF
    | RETURN
    | UNDERSCORE
    | AS
    deriving (Show, Eq, Ord)

type Action r = (AlexPosn, Char, String) -> Int -> Alex r

simpleTok :: Token -> Action Token
simpleTok tok _ _ = return tok

getS :: (AlexPosn, Char, String) -> Int -> String
getS (_, _, input) len = take len input

stringTok :: (String -> Token) -> Action Token
stringTok f inp len = return (f (getS inp len))

typeTok :: Action Token
typeTok inp len = return (TYPE (if null ns then 0 else read ns))
  where ns = drop (length "Type") (getS inp len)

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

}
