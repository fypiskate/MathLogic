{
module Lex where
}

%wrapper "basic"

$digit = 0-9
$alpha = [A-Z]
$symbols = [$alpha $digit \']

tokens :-
    $white+               ;
    &                   { \_ -> TAnd }
    \|                  { \_ -> TOr }
    "->"                { \_ -> TImplication }
    !                   { \_ -> TNot }
    \(                  { \_ -> TOpenBracket }
    \)                  { \_ -> TCloseBracket }
    "|-"                { \_ -> TCondition }
    \,                  { \_ -> TComa }
    \n                  { \_ -> TNewLine }
    $alpha [$symbols]*  { \x -> TVariable x }

{

data Token = TAnd
           | TOr
           | TImplication
           | TNot
           | TOpenBracket
           | TCloseBracket
           | TCondition
           | TComa
           | TNewLine
           | TVariable String
           deriving (Eq, Show)

}
